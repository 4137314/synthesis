import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Synthesis.Domains.Electronics.Magnetics
set_option autoImplicit false

/-! # The ideal transformer

The lossless limit of a coupled pair: a constraint between terminal variables with no
inductance, no loss and no magnetizing current. It fixes a voltage ratio and the
corresponding current ratio, conserves power at every operating point, reflects a load
impedance by the square of the turns ratio, and composes by multiplying turns ratios.

No theorem here asserts that a physical transformer is ideal; leakage, winding
resistance, core loss, saturation and bandwidth are all outside the model. -/

variable {K : Type*}

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An ideal transformer with turns ratio `n = N₂ / N₁`. It has no inductance, no loss
and no magnetizing current: it is a constraint between terminal variables. -/
structure IdealTransformer (K : Type*) [Zero K] where
  ratio : K
  nonzero : ratio ≠ 0

namespace IdealTransformer

/-- Secondary voltage forced by the turns ratio. -/
def secondaryVoltage (t : IdealTransformer K) (primaryVoltage : K) : K :=
  t.ratio * primaryVoltage

/-- Secondary current forced by the turns ratio, in the passive convention on both
sides: current entering the primary leaves the secondary. -/
def secondaryCurrent (t : IdealTransformer K) (primaryCurrent : K) : K :=
  -primaryCurrent / t.ratio

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **An ideal transformer is lossless**: the powers absorbed at the two ports cancel at
every operating point. -/
theorem power_conserved (t : IdealTransformer K) (v i : K) :
    v * i + t.secondaryVoltage v * t.secondaryCurrent i = 0 := by
  simp only [secondaryVoltage, secondaryCurrent]
  field_simp
  rw [div_self t.nonzero]
  ring

/-- **Impedance reflection**: a load `Z` on the secondary appears at the primary as
`Z / n²`. This is the identity behind impedance matching with a transformer. -/
theorem impedance_reflection (t : IdealTransformer K) {load v i : K} (current : i ≠ 0)
    (loaded : t.secondaryVoltage v = -load * t.secondaryCurrent i) :
    v / i = load / t.ratio ^ 2 := by
  have ratio := t.nonzero
  simp only [secondaryVoltage, secondaryCurrent] at loaded
  field_simp at loaded ⊢
  linear_combination loaded

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A unit-ratio transformer is a lossless pass-through of voltage. -/
theorem unit_ratio (t : IdealTransformer K) (unit : t.ratio = 1) (v : K) :
    t.secondaryVoltage v = v := by
  simp [secondaryVoltage, unit]

/-- Cascading two ideal transformers multiplies their turns ratios. -/
def cascade (first second : IdealTransformer K) : IdealTransformer K :=
  ⟨second.ratio * first.ratio, mul_ne_zero second.nonzero first.nonzero⟩

theorem cascade_voltage (first second : IdealTransformer K) (v : K) :
    (cascade first second).secondaryVoltage v =
      second.secondaryVoltage (first.secondaryVoltage v) := by
  simp only [cascade, secondaryVoltage]
  ring

end IdealTransformer

end Ordered
end Synthesis.Domains.Electronics.Magnetics
