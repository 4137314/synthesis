import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Synthesis.Domains.Electronics.Magnetics
set_option autoImplicit false

/-! # Magnetic coupling and ideal transformers

Two inductors sharing a magnetic path store the energy `(L₁ i₁² + 2 M i₁ i₂ + L₂ i₂²)/2`.
The central result is that this quadratic form is nonnegative for every pair of currents
*exactly* when `M² ≤ L₁ L₂`, so the coupling bound is not an assumption added for
convenience: it is equivalent to the passivity of the pair.

The ideal transformer is the lossless limit: it fixes a voltage ratio and the
corresponding current ratio, conserves power at every operating point, and reflects a
load impedance by the square of the turns ratio.

Leakage, winding resistance, core loss, saturation and frequency dependence are not
modelled, and no theorem here asserts that a physical transformer is ideal. -/

variable {K : Type*}

/-- A pair of magnetically coupled inductors with mutual inductance `M`. -/
structure Coupled (K : Type*) where
  primary : K
  secondary : K
  mutualInductance : K

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Coupled

/-- Flux linkage of the primary winding. -/
def primaryFlux (c : Coupled K) (i₁ i₂ : K) : K := c.primary * i₁ + c.mutualInductance * i₂

/-- Flux linkage of the secondary winding. -/
def secondaryFlux (c : Coupled K) (i₁ i₂ : K) : K := c.mutualInductance * i₁ + c.secondary * i₂

/-- Stored magnetic energy of the coupled pair. -/
def energy (c : Coupled K) (i₁ i₂ : K) : K :=
  (c.primary * i₁ ^ 2 + 2 * c.mutualInductance * i₁ * i₂ + c.secondary * i₂ ^ 2) / 2

theorem energy_flux (c : Coupled K) (i₁ i₂ : K) :
    2 * c.energy i₁ i₂ = c.primaryFlux i₁ i₂ * i₁ + c.secondaryFlux i₁ i₂ * i₂ := by
  simp only [energy, primaryFlux, secondaryFlux]
  ring

/-- Uncoupled windings store the sum of their separate energies. -/
theorem energy_uncoupled (c : Coupled K) (uncoupled : c.mutualInductance = 0) (i₁ i₂ : K) :
    c.energy i₁ i₂ = c.primary * i₁ ^ 2 / 2 + c.secondary * i₂ ^ 2 / 2 := by
  simp only [energy, uncoupled]
  ring

/-- The coupling bound is sufficient for passivity of the pair. -/
theorem energy_nonneg {c : Coupled K} (primaryPositive : 0 < c.primary)
    (bound : c.mutualInductance ^ 2 ≤ c.primary * c.secondary) (i₁ i₂ : K) : 0 ≤ c.energy i₁ i₂ := by
  have square : 0 ≤ (c.primary * i₁ + c.mutualInductance * i₂) ^ 2 := sq_nonneg _
  have residual : 0 ≤ (c.primary * c.secondary - c.mutualInductance ^ 2) * i₂ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg i₂)
  have scaled : 0 ≤ c.primary * (2 * c.energy i₁ i₂) := by
    have expand : c.primary * (2 * c.energy i₁ i₂) =
        (c.primary * i₁ + c.mutualInductance * i₂) ^ 2 + (c.primary * c.secondary - c.mutualInductance ^ 2) * i₂ ^ 2 := by
      simp only [energy]
      field_simp
      ring
    rw [expand]
    linarith
  nlinarith

/-- **The coupling bound is also necessary**: a pair whose energy is never negative
satisfies `M² ≤ L₁ L₂`. Passivity and the coupling bound are the same condition. -/
theorem coupling_bound {c : Coupled K} (primaryPositive : 0 < c.primary)
    (passive : ∀ i₁ i₂ : K, 0 ≤ c.energy i₁ i₂) : c.mutualInductance ^ 2 ≤ c.primary * c.secondary := by
  have witness := passive (-c.mutualInductance) c.primary
  have expand : c.energy (-c.mutualInductance) c.primary =
      c.primary * (c.primary * c.secondary - c.mutualInductance ^ 2) / 2 := by
    simp only [energy]
    ring
  rw [expand] at witness
  nlinarith

theorem energy_nonneg_iff {c : Coupled K} (primaryPositive : 0 < c.primary) :
    (∀ i₁ i₂ : K, 0 ≤ c.energy i₁ i₂) ↔ c.mutualInductance ^ 2 ≤ c.primary * c.secondary :=
  ⟨coupling_bound primaryPositive, fun bound => energy_nonneg primaryPositive bound⟩

end Coupled

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

section Real

/-- Coupling coefficient `k = M / sqrt (L₁ L₂)` of a pair of coupled inductors. -/
noncomputable def couplingCoefficient (c : Coupled ℝ) : ℝ :=
  c.mutualInductance / Real.sqrt (c.primary * c.secondary)

/-- **The coupling coefficient of a passive pair never exceeds unity**, which is the
usual engineering statement of the coupling bound. -/
theorem abs_coupling_le_one {c : Coupled ℝ} (primaryPositive : 0 < c.primary)
    (secondaryPositive : 0 < c.secondary)
    (bound : c.mutualInductance ^ 2 ≤ c.primary * c.secondary) : |couplingCoefficient c| ≤ 1 := by
  have product : 0 < c.primary * c.secondary := mul_pos primaryPositive secondaryPositive
  have root : 0 < Real.sqrt (c.primary * c.secondary) := Real.sqrt_pos.mpr product
  have squared : Real.sqrt (c.primary * c.secondary) ^ 2 = c.primary * c.secondary :=
    Real.sq_sqrt (le_of_lt product)
  rw [couplingCoefficient, abs_div, abs_of_pos root, div_le_one root]
  have magnitude : |c.mutualInductance| ^ 2 ≤ Real.sqrt (c.primary * c.secondary) ^ 2 := by
    rw [squared, sq_abs]
    exact bound
  nlinarith [abs_nonneg c.mutualInductance, le_of_lt root]

/-- Perfect coupling is exactly the boundary case of the passivity bound. -/
theorem coupling_one_iff {c : Coupled ℝ} (primaryPositive : 0 < c.primary)
    (secondaryPositive : 0 < c.secondary) (positiveMutual : 0 < c.mutualInductance) :
    couplingCoefficient c = 1 ↔ c.mutualInductance ^ 2 = c.primary * c.secondary := by
  have product : 0 < c.primary * c.secondary := mul_pos primaryPositive secondaryPositive
  have root : 0 < Real.sqrt (c.primary * c.secondary) := Real.sqrt_pos.mpr product
  have squared : Real.sqrt (c.primary * c.secondary) ^ 2 = c.primary * c.secondary :=
    Real.sq_sqrt (le_of_lt product)
  rw [couplingCoefficient, div_eq_one_iff_eq (ne_of_gt root)]
  constructor
  · intro equal
    rw [← squared, ← equal]
  · intro equal
    have nonneg : 0 ≤ c.mutualInductance := le_of_lt positiveMutual
    nlinarith [Real.sq_sqrt (le_of_lt product), Real.sqrt_nonneg (c.primary * c.secondary)]

end Real
end Synthesis.Domains.Electronics.Magnetics
