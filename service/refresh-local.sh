#!/usr/bin/env bash
# Refresh local demo claims and invalidate the running development server's caches.
set -euo pipefail
cd "$(dirname "$0")"

if [[ "${OTS_DEMO_DATA:-1}" == "1" && -x .venv/bin/python ]]; then
  .venv/bin/python -B seed_demo.py --refresh
fi

# Uvicorn --reload watches Python sources. A timestamp change reloads the app
# even when the commit only changed Lean, templates, metadata or documentation.
touch app/main.py
