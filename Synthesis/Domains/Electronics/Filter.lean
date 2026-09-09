import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Synthesis.Domains.Electronics.Phasor.Impedance

namespace Synthesis.Domains.Electronics.Filter
set_option autoImplicit false

/-! # First-order frequency response

The transfer functions of the two single-pole filters, and the properties a filter is
selected for: the pass-band and stop-band limits, the half-power cutoff, monotonicity of
the magnitude in frequency, and the complementarity of the low-pass and high-pass
responses at every frequency.

Magnitudes are stated as squared magnitudes through `Complex.normSq`, which keeps every
proof rational: the `-3 dB` point is the exact statement `normSq = 1/2` at the cutoff
rather than a decibel approximation, and no logarithm appears anywhere in the module.

The description is sinusoidal steady state, so it inherits every assumption of the phasor
model: a single angular frequency, linearity, decayed transients. Component tolerance,
loading by the following stage, op-amp bandwidth and noise are not modelled, and a filter
realized from these transfer functions is a specification, not a circuit. -/

open Complex

/-- Normalized frequency variable `ω / ω_c` of a single-pole response. -/
noncomputable def normalized (cutoff frequency : ℝ) : ℝ := frequency / cutoff

/-- Transfer function of a first-order low-pass response, `1 / (1 + j ω / ω_c)`. -/
noncomputable def lowPass (cutoff frequency : ℝ) : ℂ :=
  1 / (1 + Complex.I * ((normalized cutoff frequency : ℝ) : ℂ))

/-- Transfer function of a first-order high-pass response,
`(j ω / ω_c) / (1 + j ω / ω_c)`. -/
noncomputable def highPass (cutoff frequency : ℝ) : ℂ :=
  Complex.I * ((normalized cutoff frequency : ℝ) : ℂ) /
    (1 + Complex.I * ((normalized cutoff frequency : ℝ) : ℂ))

/-- Cutoff angular frequency of a resistor-capacitor pair, `1 / (R C)`. This is the
frequency at which the response reaches half power. -/
noncomputable def rcCutoff (resistance capacitance : ℝ) : ℝ := 1 / (resistance * capacitance)

theorem rcCutoff_positive {resistance capacitance : ℝ} (resistive : 0 < resistance)
    (capacitive : 0 < capacitance) : 0 < rcCutoff resistance capacitance :=
  div_pos one_pos (mul_pos resistive capacitive)

/-! ## Squared magnitudes -/

/-- The pole denominator never vanishes, so both responses are defined at every
frequency. -/
theorem pole_nonzero (cutoff frequency : ℝ) :
    1 + Complex.I * ((normalized cutoff frequency : ℝ) : ℂ) ≠ 0 := by
  intro degenerate
  have real : (1 + Complex.I * ((normalized cutoff frequency : ℝ) : ℂ)).re = 0 := by
    rw [degenerate]
    simp
  simp at real

theorem pole_normSq (cutoff frequency : ℝ) :
    Complex.normSq (1 + Complex.I * ((normalized cutoff frequency : ℝ) : ℂ)) =
      1 + normalized cutoff frequency ^ 2 := by
  simp [Complex.normSq_apply]
  ring

/-- Squared magnitude of the low-pass response, `1 / (1 + (ω / ω_c)²)`. -/
theorem lowPass_normSq (cutoff frequency : ℝ) :
    Complex.normSq (lowPass cutoff frequency) = 1 / (1 + normalized cutoff frequency ^ 2) := by
  rw [lowPass, map_div₀, pole_normSq]
  simp

/-- Squared magnitude of the high-pass response, `(ω / ω_c)² / (1 + (ω / ω_c)²)`. -/
theorem highPass_normSq (cutoff frequency : ℝ) :
    Complex.normSq (highPass cutoff frequency) =
      normalized cutoff frequency ^ 2 / (1 + normalized cutoff frequency ^ 2) := by
  rw [highPass, map_div₀, pole_normSq]
  simp [Complex.normSq_apply]
  ring

/-- **The two responses are complementary in power** at every frequency: what one passes
the other rejects, which is the defining property of a crossover pair. -/
theorem complementary (cutoff frequency : ℝ) :
    Complex.normSq (lowPass cutoff frequency) + Complex.normSq (highPass cutoff frequency) = 1 := by
  have positive : 0 < 1 + normalized cutoff frequency ^ 2 := by positivity
  rw [lowPass_normSq, highPass_normSq]
  field_simp

/-! ## Pass band, stop band and cutoff -/

/-- At zero frequency the low-pass response is exact unity gain. -/
theorem lowPass_zero (cutoff : ℝ) : lowPass cutoff 0 = 1 := by
  simp [lowPass, normalized]

/-- At zero frequency the high-pass response blocks completely. -/
theorem highPass_zero (cutoff : ℝ) : highPass cutoff 0 = 0 := by
  simp [highPass, normalized]

/-- **The half-power point.** At the cutoff frequency the low-pass response passes
exactly half the power, which is the exact form of the `-3 dB` specification. -/
theorem lowPass_cutoff {cutoff : ℝ} (positive : 0 < cutoff) :
    Complex.normSq (lowPass cutoff cutoff) = 1 / 2 := by
  have unit : normalized cutoff cutoff = 1 := div_self (ne_of_gt positive)
  rw [lowPass_normSq, unit]
  norm_num

theorem highPass_cutoff {cutoff : ℝ} (positive : 0 < cutoff) :
    Complex.normSq (highPass cutoff cutoff) = 1 / 2 := by
  have unit : normalized cutoff cutoff = 1 := div_self (ne_of_gt positive)
  rw [highPass_normSq, unit]
  norm_num

/-- The low-pass response never amplifies: its power gain is at most one at every
frequency, so a passive single-pole filter is not an active device. -/
theorem lowPass_le_one (cutoff frequency : ℝ) :
    Complex.normSq (lowPass cutoff frequency) ≤ 1 := by
  have positive : 0 < 1 + normalized cutoff frequency ^ 2 := by positivity
  rw [lowPass_normSq, div_le_one positive]
  nlinarith [sq_nonneg (normalized cutoff frequency)]

theorem highPass_le_one (cutoff frequency : ℝ) :
    Complex.normSq (highPass cutoff frequency) ≤ 1 := by
  have complement := complementary cutoff frequency
  have nonneg : 0 ≤ Complex.normSq (lowPass cutoff frequency) := Complex.normSq_nonneg _
  linarith

/-- **Monotone roll-off.** Raising the frequency never raises the low-pass gain, so the
stop band is genuinely a stop band and the response has no ripple. -/
theorem lowPass_antitone {cutoff first second : ℝ} (positive : 0 < cutoff)
    (nonneg : 0 ≤ first) (ordered : first ≤ second) :
    Complex.normSq (lowPass cutoff second) ≤ Complex.normSq (lowPass cutoff first) := by
  have firstPositive : 0 < 1 + normalized cutoff first ^ 2 := by positivity
  have secondPositive : 0 < 1 + normalized cutoff second ^ 2 := by positivity
  have scaled : normalized cutoff first ≤ normalized cutoff second := by
    simp only [normalized, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right ordered (le_of_lt (inv_pos.mpr positive))
  have firstNonneg : 0 ≤ normalized cutoff first :=
    div_nonneg nonneg (le_of_lt positive)
  rw [lowPass_normSq, lowPass_normSq, div_le_div_iff₀ secondPositive firstPositive]
  nlinarith

/-- The high-pass response rises with frequency, the dual statement. -/
theorem highPass_monotone {cutoff first second : ℝ} (positive : 0 < cutoff)
    (nonneg : 0 ≤ first) (ordered : first ≤ second) :
    Complex.normSq (highPass cutoff first) ≤ Complex.normSq (highPass cutoff second) := by
  have low := lowPass_antitone positive nonneg ordered
  have firstComplement := complementary cutoff first
  have secondComplement := complementary cutoff second
  linarith

/-- The low-pass response is strictly below unit gain away from direct current, so the
pass band is flat only in the limit. -/
theorem lowPass_lt_one {cutoff frequency : ℝ} (positive : 0 < cutoff) (excited : frequency ≠ 0) :
    Complex.normSq (lowPass cutoff frequency) < 1 := by
  have nonzero : normalized cutoff frequency ≠ 0 := by
    simp only [normalized]
    exact div_ne_zero excited (ne_of_gt positive)
  have square : 0 < normalized cutoff frequency ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 nonzero))
  have denominator : 0 < 1 + normalized cutoff frequency ^ 2 := by positivity
  rw [lowPass_normSq, div_lt_one denominator]
  linarith

end Synthesis.Domains.Electronics.Filter
