#!/usr/bin/env bash
# Start the site and the worker for local development.
set -euo pipefail
cd "$(dirname "$0")"

# The local preview includes the Satoshi/Vitalik demo board by default.
# seed_demo.py refuses databases outside the default local data directory.
if [[ "${OTS_DEMO_DATA:-1}" == "1" ]]; then
  .venv/bin/python seed_demo.py
fi

.venv/bin/python -m app.worker &
worker=$!
trap 'kill $worker' EXIT
.venv/bin/uvicorn app.main:app --port "${PORT:-8000}" --reload
