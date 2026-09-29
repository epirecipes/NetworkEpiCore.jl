#!/usr/bin/env bash
# Release gate for SA-PASS on the citable theorems (NEC-local; not synced from upstream).
#
#   bash scripts/sa_pass_citable.sh [sa_pass.sh options]
#
# Runs `scripts/sa_pass.sh --strict` (every registered required claim has SA-PASS = 1) and then
# `scripts/sa_citable_coverage.py --strict` (every name in CITABLE.txt is the `impl` of a
# registered required claim with SA-PASS = 1). `sa_pass.sh --strict` alone exits 0 when no claims
# are registered; this wrapper does not. Exit 0 only if both pass.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
PY="$(pwd)/../../.venv/bin/python"
[ -x "$PY" ] || PY="$(command -v python3)"

bash scripts/sa_pass.sh --strict "$@"
rc=$?
if [ $rc -ne 0 ]; then echo "sa_pass.sh --strict failed (exit $rc)" >&2; exit $rc; fi
"$PY" scripts/sa_citable_coverage.py --strict
