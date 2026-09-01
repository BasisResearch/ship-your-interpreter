#!/usr/bin/env bash
# Serve the residual dashboard. Serves the repo root so the page can fetch
# /experiments/residuals.tsv from the same origin.
set -euo pipefail
PORT=8642
# repo root = two levels up from this script
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
echo "Serving $ROOT on port $PORT"
echo "Open: http://localhost:${PORT}/tools/residual_dashboard/"
exec python3 -m http.server "$PORT" --directory "$ROOT"
