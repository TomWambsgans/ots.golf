"""Demo controls must not let an operator seed a production site accidentally."""
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import seed_demo


class DemoGuardTests(unittest.TestCase):
    def test_force_cannot_bypass_production_or_nonlocal_site_guard(self):
        for environment, base_url in [('production', 'https://ots.example'),
                                      ('development', 'https://ots.example')]:
            with self.subTest(environment=environment):
                config = SimpleNamespace(environment=environment, base_url=base_url)
                with patch('app.config.settings', config), patch('sys.argv', ['seed_demo.py', '--force']), \
                        patch.object(seed_demo.Base.metadata, 'create_all') as create_db:
                    with self.assertRaisesRegex(SystemExit, 'only available in development'):
                        seed_demo.main()
                    create_db.assert_not_called()


if __name__ == '__main__':
    unittest.main()
