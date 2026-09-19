#!/usr/bin/env bash
# Re-seed the local demo rows from the fixture file and reload the development server.
set -euo pipefail
cd "$(dirname "$0")"

if [[ "${OTS_PHONY:-${OTS_DEMO_DATA:-1}}" == "1" && -x .venv/bin/python ]]; then
  .venv/bin/python -B seed_demo.py
fi

# Uvicorn --reload watches Python sources. A timestamp change reloads the app
# even when the commit only changed Lean, templates, metadata or documentation.
touch app/main.py
