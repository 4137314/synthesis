#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_repository.py
lake build
lake test
lake env lean Tests/Audit.lean
