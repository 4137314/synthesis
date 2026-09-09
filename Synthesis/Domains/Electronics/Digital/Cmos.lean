import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Synthesis.Domains.Electronics.Digital
set_option autoImplicit false

/-! ## Complementary switching

An ideal complementary pair with non-overlapping thresholds never conducts from supply
to ground, which is the static-power argument for complementary logic. -/

/-- Ideal threshold model of a complementary inverter. -/
structure Complementary where
  supply : ℝ
  pullDownThreshold : ℝ
  pullUpThreshold : ℝ
  supplyPositive : 0 < supply

namespace Complementary

/-- The pull-down device conducts above its threshold. -/
def pullDownConducting (c : Complementary) (input : ℝ) : Prop := c.pullDownThreshold < input

/-- The pull-up device conducts below the complementary threshold. -/
def pullUpConducting (c : Complementary) (input : ℝ) : Prop :=
  input < c.supply - c.pullUpThreshold

/-- **No crowbar path**: when the thresholds do not overlap, no input voltage turns both
devices on, so the ideal static gate draws no supply current. -/
theorem no_static_path (c : Complementary)
    (nonOverlapping : c.supply - c.pullUpThreshold ≤ c.pullDownThreshold) (input : ℝ) :
    ¬(c.pullDownConducting input ∧ c.pullUpConducting input) := by
  rintro ⟨down, up⟩
  simp only [pullDownConducting, pullUpConducting] at down up
  linarith

/-- Outside the transition window exactly one device conducts, so the output is driven. -/
theorem low_input_pulls_up (c : Complementary) {input : ℝ}
    (low : input < c.supply - c.pullUpThreshold)
    (belowThreshold : input ≤ c.pullDownThreshold) :
    c.pullUpConducting input ∧ ¬c.pullDownConducting input := by
  refine ⟨low, ?_⟩
  simp only [pullDownConducting]
  linarith

theorem high_input_pulls_down (c : Complementary) {input : ℝ}
    (high : c.pullDownThreshold < input)
    (aboveThreshold : c.supply - c.pullUpThreshold ≤ input) :
    c.pullDownConducting input ∧ ¬c.pullUpConducting input := by
  refine ⟨high, ?_⟩
  simp only [pullUpConducting]
  linarith

end Complementary
end Synthesis.Domains.Electronics.Digital
