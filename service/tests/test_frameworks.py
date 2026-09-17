"""Framework isolation and non-destructive local demo refresh checks."""
from __future__ import annotations

import json
import re
import unittest
from unittest.mock import patch

from fastapi.testclient import TestClient
from sqlalchemy import create_engine, select
from sqlalchemy.orm import Session
from sqlalchemy.pool import StaticPool

from app import contract, github, records
from app.db import Base, Submission, User, get_session, utcnow
from app.main import app
import seed_demo


class FrameworkTests(unittest.TestCase):
    def setUp(self):
        self.engine = create_engine("sqlite://", connect_args={"check_same_thread": False}, poolclass=StaticPool)
        Base.metadata.create_all(self.engine)
        self.session = Session(self.engine, expire_on_commit=False)

        def session_dependency():
            yield self.session

        app.dependency_overrides[get_session] = session_dependency
        self.client = TestClient(app)

    def tearDown(self):
        self.client.close()
        app.dependency_overrides.clear()
        self.session.close()
        self.engine.dispose()

    def test_framework_pairs_and_foundation(self):
        self.assertEqual({k: t["slug"] for k, t in contract.framework_tracks("dag").items()},
                         {"lower": "lower", "upper": "upper"})
        self.assertEqual({k: t["slug"] for k, t in contract.framework_tracks("disclosure").items()},
                         {"lower": "disclosure-lower", "upper": "disclosure-upper"})
        self.assertEqual(contract.framework_tracks("generic"), {})
        self.assertIsNone(records.interval(self.session, "generic")["lower"])

    def test_home_records_and_chart_stay_within_framework(self):
        seed_demo.add_rows(self.session, seed_demo.ROWS)
        self.session.commit()
        for framework in ("dag", "disclosure"):
            pair = contract.framework_tracks(framework)
            expected = {"lower": pair["lower"]["baseline"] + 2, "upper": pair["upper"]["baseline"] - 5}
            response = self.client.get("/", params={"framework": framework})
            self.assertEqual(response.status_code, 200)
            html = response.text
            for kind, claim in expected.items():
                self.assertIn(f'<div class="value">{claim}<span', html)
            chart = json.loads(re.search(r'<script id="chart-points" type="application/json">(.*?)</script>',
                                         html, re.S).group(1))
            for point in chart:
                sub = self.session.get(Submission, point["id"])
                self.assertEqual(contract.track(sub.track)["framework"], framework)
            self.assertIn('location.pathname + location.search', html)
        self.assertIn('<div class="value">20<span', self.client.get("/").text)

    def test_generic_has_no_records_and_unknown_framework_is_rejected(self):
        response = self.client.get("/?framework=generic")
        self.assertEqual(response.status_code, 200)
        self.assertIn("Admission still requires", response.text)
        self.assertNotIn('id="chart-points"', response.text)
        self.assertNotIn('class="boards"', response.text)
        self.assertEqual(self.client.get("/?framework=unknown").status_code, 404)

    def test_refresh_preserves_existing_rows_and_adds_missing_tracks_once(self):
        seed_demo.add_rows(self.session, seed_demo.BASE_ROWS)
        real_user = User(login="real-solver")
        self.session.add(real_user)
        self.session.flush()
        real = Submission(track="lower", user_id=real_user.id, claim=18, status="verified",
                          source_repo="local", commit="a" * 40, baseline=True, finished_at=utcnow())
        self.session.add(real)
        self.session.commit()
        old = {s.id: (s.created_at, s.finished_at, s.record_at, s.commit, s.track)
               for s in self.session.scalars(select(Submission))}
        demo = next(s for s in self.session.scalars(select(Submission)) if s.detail_dict.get("demo"))
        demo.claim = 999
        self.session.commit()
        self.assertEqual(seed_demo.refresh(self.session), 10)
        self.assertEqual(seed_demo.refresh(self.session), 0)
        now = list(self.session.scalars(select(Submission)))
        self.assertEqual(len(now), len(seed_demo.ROWS) + 1)
        self.assertEqual(self.session.get(Submission, real.id).claim, 18)
        self.assertTrue(self.session.get(Submission, real.id).baseline)
        for sub in now:
            if sub.id in old:
                self.assertEqual((sub.created_at, sub.finished_at, sub.record_at, sub.commit, sub.track), old[sub.id])
            if sub.detail_dict.get("demo"):
                self.assertEqual(sub.claim, seed_demo.demo_claim(sub.track, sub.detail_dict["improvement"]))

    def test_disclosure_submission_links_to_its_framework(self):
        seed_demo.add_rows(self.session, [seed_demo.ROWS[-1]])
        self.session.commit()
        sub = self.session.scalar(select(Submission))
        html = self.client.get(f"/submissions/{sub.id}").text
        self.assertIn('href="/?framework=disclosure">Partial disclosures</a>', html)
        self.assertIn("Reed–Solomon", self.client.get("/rules").text)

    def test_webhook_root_mapping_includes_new_tracks_and_rejects_mixed_roots(self):
        with patch("app.github.httpx.Client") as client:
            response = client.return_value.__enter__.return_value.get.return_value
            response.json.return_value = [{"filename": "formal/Submissions/DisclosureLower/Solution.lean"}]
            self.assertEqual(github.pr_track("local/repo", 1), ("disclosure-lower", []))
            response.json.return_value += [{"filename": "formal/Submissions/Lower/Solution.lean"}]
            self.assertEqual(github.pr_track("local/repo", 1), (None, []))


if __name__ == "__main__":
    unittest.main()
