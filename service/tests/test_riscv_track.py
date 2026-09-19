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
        machine.update(slug='riscv-upper', title='RISC-V upper bound', baseline=5513,
                       cost_unit='cycles', submission_root='formal/Submissions/RiscvUpper')
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
        self.assertFalse(any(p['claim'] == 5513 for p in compression))
        self.assertEqual([(p['claim'], p['login'], p['unit']) for p in machine],
                         [(61000, 'satoshi-nakamoto', 'cycles'), (47000, 'hal-finney', 'cycles'),
                          (38000, 'ralph-merkle', 'cycles'), (30053, 'vitalik-buterin', 'cycles'),
                          (24000, 'leslie-lamport', 'cycles'), (19000, 'hal-finney', 'cycles'),
                          (15200, 'satoshi-nakamoto', 'cycles'), (12300, 'vitalik-buterin', 'cycles'),
                          (10100, 'ralph-merkle', 'cycles'), (8500, 'hal-finney', 'cycles'),
                          (7400, 'leslie-lamport', 'cycles'), (6620, 'hal-finney', 'cycles'),
                          (6510, 'vitalik-buterin', 'cycles'), (6440, 'hal-finney', 'cycles'),
                          (6370, 'vitalik-buterin', 'cycles'), (6340, 'vitalik-buterin', 'cycles'),
                          (5513, 'satoshi-nakamoto', 'cycles')])
        self.assertIn('class="chart-btn" data-chart="cycles"', html)
        self.assertIn('class="chart-panel riscv-dashboard" data-chart="cycles" hidden', html)
        self.assertIn('data-track="riscv-upper"', html)
        self.assertIn('id="riscv-upper-title"', html)
        self.assertNotIn('lower-bound frameworks.</p>', html)
        self.assertNotIn('Accepting verification cost', html)
        self.assertIn('id="riscv-upper-board-title"', html)
        self.assertIn('id="generic-upper-title"', html)
        self.assertEqual(len(re.findall('class="framework-card ', html)), 3)
        charts = [ET.fromstring(svg) for svg in re.findall(r'<svg[^>]+class="record-chart".*?</svg>', html, re.S)]
        self.assertEqual([svg.get('data-unit') for svg in charts], ['compressions', 'cycles'])
        self.assertEqual(charts[1].find('./g').get('data-series'), 'riscv-upper')
        ids = re.findall(r'\bid="([^"]+)"', html)
        self.assertEqual(len(ids), len(set(ids)))
        sub = self.session.get(Submission, machine[-1]['id'])
        detail = self.client.get(f'/submissions/{sub.id}').text
        self.assertIn('5513 cycles', detail)
        self.assertIn('every accepting execution', detail)
        self.assertIn('href="/rules#riscv-upper"', detail)
        self.assertNotIn('demo', detail)
        profile = self.client.get('/solvers/satoshi-nakamoto').text
        self.assertIn('RISC-V upper bound</a>', profile)
        self.assertIn('cycles', profile)

    def test_unlisted_machine_track_neither_opens_admission_nor_seeds_a_record(self):
        self.config['upper_tracks'] = ['generic-upper']
        self.assertIsNone(contract.riscv_upper_track())
        self.assertEqual(seed_demo.refresh(self.session), 54)
        self.assertNotIn('riscv-upper', self.client.get('/').text)
        self.assertNotIn('id="riscv-upper"', self.client.get('/rules').text)
        with self.assertRaises(HTTPException) as caught:
            queue_submission(self.session, User(login='tester'), 'riscv-upper', 'local', 'a' * 40,
                             None, [], None, None, None)
        self.assertEqual(caught.exception.status_code, 400)

    def test_machine_demo_migration_preserves_all_existing_entries(self):
        self.config['upper_tracks'] = ['generic-upper']
        seed_demo.refresh(self.session)
        before = {s.id: (s.created_at, s.finished_at, s.record_at, s.commit, s.claim)
                  for s in self.session.scalars(select(Submission))}
        self.assertEqual(len(before), 54)
        self.config['upper_tracks'].append('riscv-upper')
        self.assertEqual(seed_demo.refresh(self.session), 18)
        self.assertEqual(seed_demo.refresh(self.session), 0)
        self.assertEqual(len(list(self.session.scalars(select(Submission)))), 72)
        for identifier, original in before.items():
            s = self.session.get(Submission, identifier)
            self.assertEqual((s.created_at, s.finished_at, s.record_at, s.commit, s.claim), original)
        rows = list(self.session.scalars(select(Submission).where(Submission.track == 'riscv-upper')))
        self.assertEqual(len(rows), 18)
        machine = min(rows, key=lambda r: r.claim)
        self.assertEqual(machine.claim, contract.riscv_upper_track()['baseline'])
        self.assertEqual(machine.detail_dict['improvement'], 0)
        self.assertTrue(machine.is_record)

    def test_rules_state_accepting_bound_and_total_spec_refinement_without_scores(self):
        html = self.client.get('/rules').text
        section = re.search(r'<details id="riscv-upper">.*?</details>', html, re.S).group(0)
        for phrase in ('every accepting execution', 'Every execution must terminate',
                       'same oracle', 'raw signature bit string', 'max(1, ⌈n / 512⌉)',
                       'no additional instruction charge', 'RV64IM'):
            self.assertIn(phrase, section)
        self.assertNotIn('5513', html)
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
