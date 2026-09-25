"""The page ships a projection of the archive, not the archive: these tests pin what
the viewer is allowed to depend on, and the size that projection must stay under."""
import json
import re
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from build import FAILING_CONCLUSIONS, HEALTH_TERMS, INTERNED, SCHEMA, epoch, generate, project

APP = (ROOT / 'src/app.js').read_text()


def payload(html):
    return json.loads(re.search(r'<script id="route-data"[^>]*>(.*?)</script>', html, re.S).group(1))


class ProjectionTests(unittest.TestCase):
    def setUp(self):
        self.snapshot = json.loads((ROOT / 'data/prs.json').read_text())
        self.prs = [dict(pr, health={'score': None, 'terms': {k: 0 for k in HEALTH_TERMS},
                                     'failed': [], 'reason': 'test', 'source': None})
                    for pr in self.snapshot['prs']]
        self.rows, self.interned = project(self.prs)

    def test_rows_follow_the_schema(self):
        self.assertEqual(len(self.rows), len(self.prs))
        for row in self.rows:
            self.assertEqual(len(row), len(SCHEMA['pr']))
            self.assertEqual(len(row[SCHEMA['pr'].index('health')]), len(SCHEMA['health']))
            for check in row[SCHEMA['pr'].index('checks')]:
                self.assertEqual(len(check), len(SCHEMA['check']))
            for event in row[SCHEMA['pr'].index('events')]:
                self.assertEqual(len(event), len(SCHEMA['event']))

    def test_every_interned_index_resolves(self):
        for table in INTERNED:
            for value in self.interned[table]:
                self.assertIsInstance(value, str)
        for row in self.rows:
            for table, index in (('state', row[2]), ('reason', row[10][3])):
                self.assertGreaterEqual(index, 0, table)
                self.assertLess(index, len(self.interned[table]))
            for index in row[6] + row[10][2]:
                self.assertGreaterEqual(index, 0)

    def test_the_archive_fields_nothing_reads_never_ship(self):
        html = generate()
        for field in ('review_boards', 'review_events', 'updated_at', 'scopeReset'):
            self.assertNotIn(f'"{field}"', html, field)
        # every absolute URL inside the payload would be the same prefix, so only the
        # failed checks keep their source link and every other record drops it
        data = payload(html)
        checks = [c for row in data['prs'] for c in row[SCHEMA['pr'].index('checks')]]
        self.assertTrue(checks)
        for check in checks:
            url = check[SCHEMA['check'].index('url')]
            self.assertTrue(url is None or url.startswith('https://github.com/'), url)

    def test_timestamps_are_milliseconds(self):
        # milliseconds, not seconds: the archive's ISO strings become epoch ints so the
        # high-count records lose the repeated punctuation of the ISO form
        value = epoch('2026-09-05T00:00:00Z')
        self.assertIsInstance(value, int)
        self.assertGreater(value, 1_000_000_000_000, "seconds, not milliseconds")
        self.assertLess(value, 4_000_000_000_000)
        self.assertIsNone(epoch(None))
        row = self.rows[0]
        self.assertIsInstance(row[SCHEMA['pr'].index('created')], int)
        events = row[SCHEMA['pr'].index('events')]
        if events:
            self.assertIsInstance(events[0][SCHEMA['event'].index('at')], int)

    def test_the_viewer_decodes_every_column(self):
        """app.js indexes the schema by name, so the projection cannot rename a column."""
        for column in SCHEMA['pr']:
            self.assertIn(column, APP, column)
        for table in INTERNED:
            self.assertIn(f'"{table}"', APP, table)

    def test_the_payload_stays_small(self):
        data = payload(generate())
        size = len(json.dumps(data, separators=(',', ':')).encode())
        self.assertLess(size, 400_000, f"payload grew to {size:,} bytes")


if __name__ == '__main__':
    unittest.main()
