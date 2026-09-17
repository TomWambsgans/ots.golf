#!/usr/bin/env bash
# Start the site and the worker for local development (dev login enabled).
set -euo pipefail
cd "$(dirname "$0")"

.venv/bin/python -m app.worker &
worker=$!
trap 'kill $worker' EXIT
.venv/bin/uvicorn app.main:app --port "${PORT:-8000}" --reload
