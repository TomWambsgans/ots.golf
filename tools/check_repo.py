#!/usr/bin/env python3
"""Run local regression checks without network access or changing the running site.

    python3 tools/check_repo.py --numerics-python .venv-tools/bin/python --formal --paper

Requires the service environment and NumPy for the research-tool tests. --official runs all
five certificate pipelines after building Lean. Linux sandbox acceptance and the browser check
are separate commands: verifier/check_linux_sandbox.py and service/browser_check.py.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--service-python', default=str(ROOT / 'service/.venv/bin/python'))
    parser.add_argument('--numerics-python', default=sys.executable)
    parser.add_argument('--node', help='Node.js executable for JavaScript syntax checks (otherwise found on PATH)')
    parser.add_argument('--formal', action='store_true', help='build Lean and audit all protected model declarations')
    parser.add_argument('--official', action='store_true', help='also run all five official certificate pipelines')
    parser.add_argument('--paper', action='store_true', help='compile the DAG paper with latexmk')
    args = parser.parse_args()
    service_python = shutil.which(args.service_python)
    numerics_python = shutil.which(args.numerics_python)
    node = shutil.which(args.node or 'node')
    if not service_python or not numerics_python:
        parser.error('Python environment missing; see service/README.md and tools/README.md')
    if subprocess.run([numerics_python, '-c', 'import numpy'], capture_output=True).returncode:
        parser.error('NumPy is missing from --numerics-python; see tools/README.md')
    if not node:
        parser.error('Node.js is required for syntax checks; install it or pass --node /path/to/node')

    def check(label: str, command: list[str], cwd: Path = ROOT) -> None:
        print(f'\nChecking {label}', flush=True)
        subprocess.run(command, cwd=cwd, check=True)

    try:
        check('contract pin', [sys.executable, 'verifier/pin_contract.py', 'check'])
        check('verifier regression tests', [sys.executable, '-m', 'unittest', 'discover', '-s', 'verifier/tests', '-v'])
        check('service regression tests', [service_python, '-m', 'unittest', 'discover', '-s', 'tests', '-v'], ROOT / 'service')
        check('numerical regressions', [numerics_python, '-m', 'unittest', 'discover', '-s', 'tools/tests', '-v'])
        for script in sorted((ROOT / 'service/app/static').glob('*.js')):
            check(script.name, [node, '--check', str(script)])
        for parent in ('service', 'service/deploy', 'verifier'):
            for script in sorted((ROOT / parent).glob('*.sh')):
                check(str(script.relative_to(ROOT)), ['bash', '-n', str(script)])
        if args.formal or args.official:
            check('Lean library and submissions', ['lake', 'build', 'OptimalOTS', 'Submissions'], ROOT / 'formal')
            check('protected model axioms', ['lake', 'env', 'lean', 'scripts/check-axioms.lean'], ROOT / 'formal')
        if args.official:
            import json
            cfg = json.loads((ROOT / 'challenges.json').read_text())
            for track in cfg['tracks']:
                check(f"official certificate {track['slug']}",
                      [sys.executable, 'verifier/verify.py', track['slug'], '--source', str(ROOT)])
        if args.paper:
            check('paper', ['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                            'looking-for-optimal-OTS.tex'], ROOT / 'paper')
    except (subprocess.CalledProcessError, OSError) as error:
        print(f'Check failed: {error}', file=sys.stderr)
        return 1
    print('\nRequested local checks passed. Browser and Linux deployment acceptance are separate checks.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
