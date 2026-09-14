"""Evidence boundaries and reproducibility for the route-map pipeline."""
import copy
import json
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from build import generate, health, validate
from refresh import merge_observations, utc_timestamp

class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.roadmap = json.loads((ROOT / 'data/roadmap.json').read_text())
        self.selection = json.loads((ROOT / 'data/selection.json').read_text())
        self.snapshot = json.loads((ROOT / 'data/prs.json').read_text())

    def test_timestamps_require_utc_data(self):
        snapshot = copy.deepcopy(self.snapshot)
        snapshot['prs'][0]['created_at'] = '2026-09-13T18:00:00+08:00'
        with self.assertRaisesRegex(AssertionError, 'Source timestamps must be UTC'):
            validate(self.roadmap, self.selection, snapshot)
        snapshot['prs'][0]['created_at'] = '2026-09-13T10:00:00'
        with self.assertRaisesRegex(AssertionError, 'Source timestamps must be UTC'):
            validate(self.roadmap, self.selection, snapshot)

    def test_collector_normalizes_instants_without_guessing_zone(self):
        self.assertEqual(utc_timestamp('2026-09-13T18:00:00+08:00'), '2026-09-13T10:00:00Z')
        with self.assertRaisesRegex(ValueError, 'explicit timezone'):
            utc_timestamp('2026-09-13T10:00:00')

    def test_unrelated_pr_rejected(self):
        selection = copy.deepcopy(self.selection)
        selection[0].update(worked=False, reviewed=False)
        with self.assertRaisesRegex(AssertionError, 'Unrelated PR'):
            validate(self.roadmap, selection, self.snapshot)

    def test_new_selection_needs_refresh(self):
        selection = copy.deepcopy(self.selection)
        selection.append({**selection[0], 'number': 999999})
        with self.assertRaisesRegex(AssertionError, 'Refresh the snapshot'):
            validate(self.roadmap, selection, self.snapshot)

    def test_stale_head_never_scores_100(self):
        pr = copy.deepcopy(next(p for p in self.snapshot['prs'] if p['number'] == 6203))
        self.assertEqual(health(pr)['score'], 100)
        pr['head'] = 'a' * 40
        self.assertIsNone(health(pr)['score'])

    def test_absent_rubric_is_not_a_failure_or_complete_review(self):
        pr = copy.deepcopy(next(p for p in self.snapshot['prs'] if p['number'] == 6203))
        for board in pr['review_boards']:
            board['states']['reuse'] = 'absent'
        result = health(pr)
        self.assertEqual(result['terms']['D'], 0)
        self.assertIsNone(result['score'])

    def test_overwritten_observations_preserved_once(self):
        old = {'at': '2026-09-01T00:00:00Z', 'verdict': 'block', 'round': 1}
        new = {'at': '2026-09-02T00:00:00Z', 'verdict': 'approve', 'round': 2}
        self.assertEqual(merge_observations([old], [old, new]), [old, new])

    def test_open_conjecture_cannot_be_a_proof_summit(self):
        roadmap = copy.deepcopy(self.roadmap)
        roadmap["routes"][2]["summits"] = ["zeeman"]
        with self.assertRaisesRegex(AssertionError, "proof summit"):
            validate(roadmap, self.selection, self.snapshot)

    def test_checkpoint_must_belong_to_its_route(self):
        roadmap = copy.deepcopy(self.roadmap)
        roadmap["routes"][0]["checkpoints"][0]["nodes"] = ["zeeman"]
        with self.assertRaisesRegex(AssertionError, "Checkpoint lies outside"):
            validate(roadmap, self.selection, self.snapshot)

    def test_merged_tree_keeps_every_proof_endpoint(self):
        roadmap = copy.deepcopy(self.roadmap)
        roadmap["routes"][0]["tree"]["children"].pop()
        with self.assertRaisesRegex(AssertionError, "route tree must branch|Every proof summit"):
            validate(roadmap, self.selection, self.snapshot)

    def test_generated_file_matches_inputs(self):
        self.assertEqual(generate(), (ROOT / 'geotopo-route-map.html').read_text())

if __name__ == '__main__':
    unittest.main()
