#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Fetch only the Mathlib import closure used by the real-valued and electronics models.
lake exe cache get \
  Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Algebra.Order.BigOperators.Ring.Finset \
  Mathlib.Algebra.Order.Field.Basic \
  Mathlib.Analysis.Calculus.Deriv.Add \
  Mathlib.Analysis.Calculus.Deriv.Inv \
  Mathlib.Analysis.Calculus.Deriv.Mul \
  Mathlib.Analysis.Calculus.MeanValue \
  Mathlib.Analysis.Complex.Norm \
  Mathlib.Analysis.Complex.Trigonometric \
  Mathlib.Analysis.SpecialFunctions.ExpDeriv \
  Mathlib.Analysis.SpecialFunctions.Log.Basic \
  Mathlib.Analysis.SpecialFunctions.Sqrt \
  Mathlib.Data.Fintype.BigOperators \
  Mathlib.Data.Real.Basic \
  Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus \
  Mathlib.Order.Filter.AtTopBot.Basic \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.GCongr \
  Mathlib.Tactic.LinearCombination \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Positivity \
  Mathlib.Tactic.Ring
