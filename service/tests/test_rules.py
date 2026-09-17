"""Rules describe the contract independently of leaderboard and candidate claims."""
from __future__ import annotations

import copy
import re
import unittest
from unittest.mock import patch

from fastapi.testclient import TestClient

from app import contract
from app.main import app


class RulesTests(unittest.TestCase):
    def setUp(self):
        self.client = TestClient(app)

    def tearDown(self):
        self.client.close()

    def rules_body(self):
        response = self.client.get('/rules')
        self.assertEqual(response.status_code, 200)
        return re.search(r'<main>(.*?)</main>', response.text, re.S).group(1)

    def test_rules_do_not_publish_scores_or_candidate_history(self):
        config = copy.deepcopy(contract.load())
        for track in config['tracks']:
            track['baseline'] = 987654
        with patch.object(contract, 'load', return_value=config), \
             patch.object(contract, 'generic_lower_certificate', return_value={'claim': 765432}), \
             patch.object(contract, 'generic_upper_candidate', return_value={'claim': 876543}):
            html = self.rules_body()
        self.assertNotRegex(html, r'\b(?:18|80|106|987654|876543|765432)\b')
        self.assertNotIn('Certified lower baselines', html)
        self.assertNotIn('Current candidate', html)
        self.assertNotIn('baseline', html)
        self.assertNotIn('proof history', html)

    def test_rules_preserve_framework_links_and_admission_scope(self):
        html = self.rules_body()
        for anchor in ('generic-algorithms', 'generic-upper', 'graph', 'partial-disclosures',
                       'legacy-certificates', 'hash', 'security', 'params', 'cut', 'play', 'rules'):
            self.assertIn(f'id="{anchor}"', html)
        self.assertIn('Three lower-bound frameworks', html)
        self.assertIn('One upper track: generic algorithms', html)
        self.assertIn('Reed–Solomon', html)
        self.assertIn('46 distinct hash origins', html)
        self.assertIn('<strong>Open:</strong> DAG lower and partial-disclosure lower.', html)
        self.assertIn('<strong>Pending:</strong> generic lower and upper', html)
        self.assertIn('Their submission roots are closed.', html)
        self.assertIn('AGENTS.md#what-a-submission-exports', html)
        self.assertIn('formal/OptimalOTS/Statement.lean', html)
        self.assertIn('formal/OptimalOTS/Disclosure.lean', html)


if __name__ == '__main__':
    unittest.main()
