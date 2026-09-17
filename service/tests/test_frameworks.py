"""Framework isolation and non-destructive local demo refresh checks."""
from __future__ import annotations

import json
import re
import unittest
import xml.etree.ElementTree as ET
from unittest.mock import patch

from fastapi.testclient import TestClient
from fastapi import HTTPException
from sqlalchemy import create_engine, select
from sqlalchemy.orm import Session
from sqlalchemy.pool import StaticPool

from app import contract, github, records
from app.db import Base, Submission, User, get_session, utcnow
from app.main import app, queue_submission
import seed_demo


class FrameworkTests(unittest.TestCase):
    maxDiff = 1500

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

    def chart(self, html):
        return json.loads(re.search(r'<script id="chart-points" type="application/json">(.*?)</script>',
                                    html, re.S).group(1))

    def chart_svg(self, html):
        return ET.fromstring(re.search(r'<svg[^>]+class="record-chart".*?</svg>', html, re.S).group(0))

    def test_combined_chart_keeps_records_attributed_and_board_filters_independent(self):
        seed_demo.add_rows(self.session, seed_demo.ROWS)
        self.session.commit()
        for framework in ("all", "dag", "disclosure", "generic"):
            response = self.client.get("/", params={"framework": framework})
            self.assertEqual(response.status_code, 200)
            html = response.text
            points = self.chart(html)
            self.assertEqual({p['framework'] for p in points}, {'dag', 'disclosure'})
            self.assertEqual({p['kind'] for p in points}, {'lower'})
            for point in points:
                sub = self.session.get(Submission, point["id"])
                self.assertEqual(contract.track(sub.track)["framework"], point['framework'])
                self.assertEqual(sub.claim, point['claim'])
                self.assertTrue(point['demo'])
            tables = set(re.findall(r'<table class="lb-table" data-track="([^"]+)"', html))
            expected = {t['slug'] for t in contract.tracks()
                        if t['kind'] == 'lower' and (framework == 'all' or t['framework'] == framework)}
            self.assertEqual(tables, expected)
        html = self.client.get('/').text
        self.assertEqual(len(re.findall(r'<table class="lb-table"', html)), 2)
        self.assertEqual(len(re.findall(r'<article class="framework-card ', html)), 3)

    def test_three_lower_series_with_generic_pending_outside_numeric_axis(self):
        response = self.client.get("/?framework=generic")
        self.assertEqual(response.status_code, 200)
        svg = self.chart_svg(response.text)
        lower = svg.findall("./g[@data-kind='lower']")
        self.assertEqual({s.get('data-series') for s in lower}, {'generic-lower', 'lower', 'disclosure-lower'})
        pending = svg.find("./g[@data-series='generic-lower']")
        self.assertEqual(pending.get('data-status'), 'pending')
        self.assertEqual(pending.findall('.//circle'), [])
        self.assertEqual(self.chart(response.text), [])
        axis_y = float(svg.find("./line[@class='axis']").get('y1'))
        lane_y = float(re.search(r'M[\d.]+,([\d.]+)', pending.find('path').get('d')).group(1))
        self.assertGreater(lane_y, axis_y)
        self.assertTrue('No certified generic lower bound yet' in response.text)
        self.assertEqual(self.client.get("/?framework=unknown").status_code, 404)

    def test_single_generic_upper_is_a_candidate_not_an_inherited_record(self):
        seed_demo.add_rows(self.session, seed_demo.ROWS)
        self.session.commit()
        html = self.client.get('/').text
        svg = self.chart_svg(html)
        uppers = svg.findall("./g[@data-kind='upper']")
        self.assertEqual(len(uppers), 1)
        self.assertEqual(uppers[0].get('data-series'), 'generic-upper')
        self.assertEqual(uppers[0].get('data-status'), 'candidate')
        self.assertEqual(uppers[0].find("text[@class='label']").text, 'Generic upper candidate 106')
        self.assertEqual(uppers[0].findall('.//circle'), [])
        self.assertTrue('Cost and security checked; correctness and signing availability pending' in html)
        self.assertFalse('data-track="disclosure-upper"' in html)

    def test_baselines_render_without_records(self):
        html = self.client.get('/').text
        svg = self.chart_svg(html)
        for slug, baseline in [('lower', 18), ('disclosure-lower', 80)]:
            group = svg.find(f"./g[@data-series='{slug}']")
            self.assertEqual(group.get('data-status'), 'certified')
            self.assertTrue(str(baseline) in group.find('path/title').text)
        self.assertFalse('Local demo leaderboard' in html)

    def test_rules_use_certified_baselines_even_when_demo_records_are_higher(self):
        seed_demo.add_rows(self.session, seed_demo.ROWS)
        self.session.commit()
        html = self.client.get('/rules').text
        table = re.search(r'<table class="framework-comparison">(.*?)</table>', html, re.S).group(1)
        cells = re.findall(r'<td>(\d+)</td>', table)
        self.assertEqual(cells, ['18', '80'])
        self.assertTrue('Reed–Solomon' in html)
        self.assertTrue('id="generic-algorithms"' in html)
        self.assertTrue('outside the numeric axis' in html)

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
        self.assertTrue('href="/?framework=disclosure#lower">Partial disclosures</a>' in html)
        self.assertTrue('This demo claim is not a kernel-verified result' in html)

    def test_solver_page_names_framework_and_bound_kind(self):
        seed_demo.add_rows(self.session, seed_demo.ROWS)
        self.session.commit()
        html = self.client.get('/solvers/satoshi-nakamoto').text
        self.assertTrue('href="/?framework=dag#lower">DAG</a>' in html)
        self.assertTrue('href="/rules#legacy-certificates">Partial disclosures reference</a>' in html)
        self.assertTrue('Lower bound' in html and 'Legacy upper certificate' in html)

    def test_public_submission_queue_does_not_admit_legacy_upper_tracks(self):
        for track in ('upper', 'disclosure-upper'):
            with self.assertRaises(HTTPException) as caught:
                queue_submission(self.session, User(login='tester'), track, 'local', 'a' * 40,
                                 None, [], None, None, None)
            self.assertEqual(caught.exception.status_code, 400)
            self.assertTrue('generic algorithm framework' in caught.exception.detail)
        self.assertEqual(list(self.session.scalars(select(Submission))), [])

    def test_webhook_root_mapping_includes_new_tracks_and_rejects_mixed_roots(self):
        with patch("app.github.httpx.Client") as client:
            response = client.return_value.__enter__.return_value.get.return_value
            response.json.return_value = [{"filename": "formal/Submissions/DisclosureLower/Solution.lean"}]
            self.assertEqual(github.pr_track("local/repo", 1), ("disclosure-lower", []))
            response.json.return_value += [{"filename": "formal/Submissions/Lower/Solution.lean"}]
            self.assertEqual(github.pr_track("local/repo", 1), (None, []))


if __name__ == "__main__":
    unittest.main()
