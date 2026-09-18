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
        return re.search(r'<main\b[^>]*>(.*?)</main>', response.text, re.S).group(1)

    def test_rules_do_not_publish_scores_or_candidate_history(self):
        config = copy.deepcopy(contract.load())
        for track in config['tracks']:
            track['baseline'] = 987654
        with patch.object(contract, 'load', return_value=config):
            html = self.rules_body()
        self.assertNotRegex(re.sub(r'<[^>]*>', ' ', html), r'\b(?:18|80|93|106|987654|876543|765432)\b')
        self.assertNotIn('Certified lower baselines', html)
        self.assertNotIn('Current candidate', html)
        self.assertNotIn('baseline', html)
        self.assertNotIn('proof history', html)

    def test_rules_preserve_framework_links_and_admission_scope(self):
        html = self.rules_body()
        for anchor in ('generic-algorithms', 'generic-upper', 'graph', 'partial-disclosures', 'whole-words',
                       'legacy-certificates', 'hash', 'security', 'params', 'cut', 'play', 'rules',
                       'generic-admissibility', 'dag-model', 'whole-word-model', 'submission-format'):
            self.assertIn(f'id="{anchor}"', html)
        self.assertIn('What are we optimizing?', html)
        self.assertIn('<strong>Upper bound.</strong>', html)
        self.assertIn('<strong>Lower bound.</strong>', html)
        self.assertIn('whole 128-bit words', html)
        self.assertIn('41 words', html)
        self.assertIn('No other deterministic', html)
        self.assertNotIn('hash origins', html)
        self.assertNotIn('Reed–Solomon', html)
        self.assertIn('Submit an upper-bound construction, or a lower-bound proof', html)
        self.assertNotIn('<strong>Pending:</strong>', html)
        self.assertIn('signing failure is at most <strong>1/2 for lower bounds</strong>', html)
        self.assertIn('<strong>2<sup>−128</sup> for upper constructions</strong>', html)
        self.assertIn('returned signatures are rejected with probability zero', html)
        self.assertIn('formal/Submissions/GenericUpper/', html)
        self.assertIn('formal/Submissions/GenericLower/', html)
        self.assertNotIn('Their submission roots are closed.', html)
        self.assertIn('AGENTS.md#what-a-submission-exports', html)
        self.assertIn('formal/OptimalOTS/Statement.lean', html)
        self.assertIn('formal/OptimalOTS/AlgorithmWeak.lean', html)
        self.assertIn('formal/OptimalOTS/WholeWords.lean', html)

    def test_whole_word_diagram_keeps_variable_input_length_and_two_hash_halves(self):
        html = self.rules_body()
        diagram = re.search(r'<svg[^>]*aria-labelledby="words-figure-title words-figure-desc".*?</svg>',
                            html, re.S).group(0)
        self.assertIn('256 bits', diagram)
        self.assertIn('low 128 bits', diagram)
        self.assertIn('high 128 bits', diagram)
        self.assertIn('Any number of words', diagram)
        self.assertIn('n whole words', diagram)
        self.assertNotIn('origins-figure-title', html)
        self.assertIn('cut-figure-title', html)


if __name__ == '__main__':
    unittest.main()
