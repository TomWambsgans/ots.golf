"""Chart rendering remains bounded, accessible and safe for submitted attribution."""
from __future__ import annotations

from datetime import datetime, timedelta
import json
import unittest
import xml.etree.ElementTree as ET

from app.charts import _nice_ticks, record_chart


class ChartTests(unittest.TestCase):
    def test_axis_size_is_bounded_through_maximum_admissible_claim(self):
        for high in (1, 18, 93, 106, 250, 1000, 1_000_000):
            with self.subTest(high=high):
                ticks = _nice_ticks(0, high)
                self.assertLessEqual(len(ticks), 9)
                self.assertEqual(ticks, sorted(set(ticks)))
                self.assertTrue(all(0 <= tick <= high for tick in ticks))
        chart = record_chart([self.series(1_000_000)], datetime(2026, 1, 1))
        self.assertLess(len(chart['svg']), 6000)

    @staticmethod
    def series(claim=93, points=None):
        return {'slug': 'disclosure-lower', 'framework': 'disclosure', 'kind': 'lower',
                'label': 'Generality 1/3 lower', 'baseline': claim, 'points': points or []}

    def test_attribution_cannot_escape_svg_or_json_script(self):
        stamp = datetime(2026, 1, 1)
        login = '</script><script>alert("x")</script>'
        point = {'t': stamp, 'claim': 93, 'login': login, 'id': 'a" onload="bad', 'demo': True}
        chart = record_chart([self.series(points=[point])], stamp + timedelta(days=1))
        svg = ET.fromstring(chart['svg'])
        self.assertEqual(svg.get('role'), 'group')
        self.assertEqual(svg.findall('.//script'), [])
        self.assertNotIn('<', chart['points'])
        self.assertEqual(json.loads(chart['points'])[0]['login'], login)
        link = svg.find('.//a')
        self.assertIn(login, link.get('aria-label'))
        self.assertNotIn('onload', link.attrib)

    def test_equal_endpoint_labels_remain_separate(self):
        series = [dict(self.series(93), slug=slug) for slug in ('first', 'second', 'third')]
        svg = ET.fromstring(record_chart(series, datetime(2026, 1, 1))['svg'])
        ys = [float(t.get('y')) for t in svg.findall("./g/text[@class='label']")]
        self.assertEqual(len(set(ys)), 3)
        self.assertGreaterEqual(min(abs(a - b) for i, a in enumerate(ys) for b in ys[i + 1:]), 28)

    def test_future_timestamp_is_inside_chart_axis(self):
        now = datetime(2026, 1, 1)
        point = {'t': now + timedelta(minutes=2), 'claim': 93, 'login': 'solver', 'id': 'id'}
        chart = record_chart([self.series(points=[point])], now)
        svg = ET.fromstring(chart['svg'])
        axis_right = float(svg.find("./line[@class='axis']").get('x2'))
        self.assertLessEqual(json.loads(chart['points'])[0]['x'], axis_right)


if __name__ == '__main__':
    unittest.main()
