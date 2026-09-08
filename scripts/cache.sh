#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Fetch only the Mathlib import closure used by the real-valued model.
lake exe cache get Mathlib.Data.Real.Basic Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
