"""The machine track has explicit admission and an independent cycle scale."""
from __future__ import annotations

import copy
import json
import re
import unittest
import xml.etree.ElementTree as ET
from unittest.mock import patch

from fastapi import HTTPException
from fastapi.testclient import TestClient
from sqlalchemy import create_engine, select
from sqlalchemy.orm import Session
from sqlalchemy.pool import StaticPool

from app import contract
from app.db import Base, Submission, User, get_session
from app.main import app, queue_submission
import seed_demo


class RiscvTrackTests(unittest.TestCase):
    def setUp(self):
        self.config = copy.deepcopy(contract.load())
        machine = copy.deepcopy(next(t for t in self.config['tracks'] if t['slug'] == 'generic-upper'))
        machine.update(slug='riscv-upper', title='RISC-V upper bound', baseline=229113,
                       cost_unit='virtual cycles', submission_root='formal/Submissions/RiscvUpper')
        self.config['tracks'] = [t for t in self.config['tracks'] if t['slug'] != 'riscv-upper'] + [machine]
        self.config['upper_tracks'] = ['generic-upper', 'riscv-upper']
        for framework in self.config['frameworks']:
            framework.pop('upper_track', None)
        self.config_patch = patch.object(contract, 'load', return_value=self.config)
        self.config_patch.start()
        self.addCleanup(self.config_patch.stop)
        self.engine = create_engine('sqlite://', connect_args={'check_same_thread': False}, poolclass=StaticPool)
        Base.metadata.create_all(self.engine)
        self.session = Session(self.engine, expire_on_commit=False)
        app.dependency_overrides[get_session] = lambda: self.session
        self.client = TestClient(app)

    def tearDown(self):
        self.client.close()
        app.dependency_overrides.clear()
        self.session.close()
        self.engine.dispose()

    @staticmethod
    def points(html, identifier):
        return json.loads(re.search(rf'<script id="{identifier}" type="application/json">(.*?)</script>',
                                    html, re.S).group(1))

    def test_second_upper_track_has_separate_units_and_record_attribution(self):
        seed_demo.refresh(self.session)
        html = self.client.get('/').text
        compression = self.points(html, 'chart-points')
        machine = self.points(html, 'riscv-chart-points')
        self.assertTrue(all(p['unit'].startswith('compression') for p in compression))
        self.assertFalse(any(p['claim'] == 229113 for p in compression))
        self.assertEqual([(p['claim'], p['login'], p['unit']) for p in machine],
                         [(229113, 'satoshi-nakamoto', 'virtual cycles')])
        self.assertIn('data-track="riscv-upper"', html)
        self.assertIn('id="riscv-upper-title"', html)
        self.assertIn('id="riscv-upper-board-title"', html)
        self.assertIn('id="generic-upper-title"', html)
        self.assertEqual(len(re.findall('class="framework-card ', html)), 3)
        charts = [ET.fromstring(svg) for svg in re.findall(r'<svg[^>]+class="record-chart".*?</svg>', html, re.S)]
        self.assertEqual([svg.get('data-unit') for svg in charts], ['compressions', 'virtual cycles'])
        self.assertEqual(charts[1].find('./g').get('data-series'), 'riscv-upper')
        ids = re.findall(r'\bid="([^"]+)"', html)
        self.assertEqual(len(ids), len(set(ids)))
        sub = self.session.get(Submission, machine[0]['id'])
        detail = self.client.get(f'/submissions/{sub.id}').text
        self.assertIn('229113 virtual cycles', detail)
        self.assertIn('every accepting execution', detail)
        self.assertIn('href="/rules#riscv-upper"', detail)
        self.assertIn('Verification status: unverified.', detail)
        self.assertNotIn('s-verified', detail)
        profile = self.client.get('/solvers/satoshi-nakamoto').text
        self.assertIn('RISC-V upper bound</a>', profile)
        self.assertIn('virtual cycles', profile)

    def test_unlisted_machine_track_neither_opens_admission_nor_seeds_a_record(self):
        self.config['upper_tracks'] = ['generic-upper']
        self.assertIsNone(contract.riscv_upper_track())
        self.assertEqual(seed_demo.refresh(self.session), 21)
        self.assertNotIn('riscv-upper', self.client.get('/').text)
        self.assertNotIn('id="riscv-upper"', self.client.get('/rules').text)
        with self.assertRaises(HTTPException) as caught:
            queue_submission(self.session, User(login='tester'), 'riscv-upper', 'local', 'a' * 40,
                             None, [], None, None, None)
        self.assertEqual(caught.exception.status_code, 400)

    def test_machine_demo_migration_preserves_all_twenty_one_existing_entries(self):
        self.config['upper_tracks'] = ['generic-upper']
        seed_demo.refresh(self.session)
        before = {s.id: (s.created_at, s.finished_at, s.record_at, s.commit, s.claim)
                  for s in self.session.scalars(select(Submission))}
        self.assertEqual(len(before), 21)
        self.config['upper_tracks'].append('riscv-upper')
        self.assertEqual(seed_demo.refresh(self.session), 1)
        self.assertEqual(seed_demo.refresh(self.session), 0)
        self.assertEqual(len(list(self.session.scalars(select(Submission)))), 22)
        for identifier, original in before.items():
            s = self.session.get(Submission, identifier)
            self.assertEqual((s.created_at, s.finished_at, s.record_at, s.commit, s.claim), original)
        machine = self.session.scalar(select(Submission).where(Submission.track == 'riscv-upper'))
        self.assertEqual(machine.claim, contract.riscv_upper_track()['baseline'])
        self.assertEqual(machine.detail_dict['improvement'], 0)

    def test_rules_state_accepting_bound_and_total_spec_refinement_without_scores(self):
        html = self.client.get('/rules').text
        section = re.search(r'<details id="riscv-upper">.*?</details>', html, re.S).group(0)
        for phrase in ('every accepting execution', 'Every execution must terminate',
                       'same oracle', 'raw signature bit string', 'max(1, ⌈n / 512⌉)',
                       'no additional instruction charge', 'RV64IM', '256 output bits'):
            self.assertIn(phrase, section)
        self.assertNotIn('229113', html)
        self.assertNotRegex(html, r'<details\b[^>]*\bopen\b')
        self.assertIn('formal/Submissions/RiscvUpper/', html)
        self.assertIn('<code>riscv-upper</code>', html)

    def test_machine_admission_is_independent_of_lower_framework_links(self):
        self.assertTrue(all(set(contract.framework_tracks(f['slug'])) == {'lower'}
                            for f in self.config['frameworks']))
        self.assertEqual([t['slug'] for t in contract.upper_tracks()], ['generic-upper', 'riscv-upper'])
        user = User(login='machine-solver')
        self.session.add(user)
        self.session.commit()
        sub = queue_submission(self.session, user, 'riscv-upper', 'local', 'a' * 40,
                               'Machine proof', [], None, None, None)
        self.assertEqual((sub.track, sub.status), ('riscv-upper', 'pending'))
        self.assertIn(f'href="/submissions/{sub.id}"', self.client.get('/').text)


if __name__ == '__main__':
    unittest.main()
