#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export MATHLIB_NO_CACHE_ON_UPDATE=1
# Presentation only: proof checking remains in scripts/check.sh.
export DISABLE_EQUATIONS=1
export LEAN_NUM_THREADS="${SYNTHESIS_DOC_THREADS:-2}"
lake -d docbuild build doc-gen4
# One extractor at a time; do not rebuild all imported Mathlib API pages.
lake -d docbuild env python3 scripts/build_docs.py
python3 scripts/check_docs.py
