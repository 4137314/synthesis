import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Synthesis.Domains.Electronics.Phasor.Impedance

namespace Synthesis.Domains.Electronics.Power
set_option autoImplicit false

/-! # Power in sinusoidal steady state

Two descriptions of the same quantity, kept separate on purpose.

The first is the time-domain one. `instantaneous_decomposition` proves that the product
of two sinusoids of the same frequency splits exactly into a constant term and a term at
twice the frequency. That identity is what makes "average power" meaningful: the constant
term is `V I cos φ / 2`, and the oscillating term contributes nothing over a whole number
of periods. The averaging step itself is *not* proved here — it needs an integral over a
period, which this module does not take — so the constant term is identified as the
average by the decomposition and by the explicit statement of that reading, not by a
proved limit.

The second is the phasor one. Complex power `S = V conj(I) / 2` has the dissipated power
as its real part and the exchanged reactive power as its imaginary part, and
`apparent_sq` proves the power triangle `|S|² = P² + Q²` as an identity rather than a
picture. Passivity, the vanishing of dissipation in a pure reactance, and the unit bound
on the power factor all follow from the impedance alone.

Everything presupposes the phasor model: a single angular frequency, linearity and
decayed transients. Harmonics, distortion, and the power drawn by a nonlinear load are
outside it, and the power factor defined here is the displacement factor only. -/

open Complex

/-! ## Time domain -/

/-- **Product-to-sum decomposition of instantaneous power.** The product of a voltage
and a current sinusoid of the same angular frequency is a constant plus a term at twice
the frequency. The constant `V I cos φ / 2` is the average power over a period and the
oscillating part is the energy exchanged back and forth within it. -/
theorem instantaneous_decomposition (voltageAmplitude currentAmplitude frequency phase t : ℝ) :
    voltageAmplitude * Real.cos (frequency * t + phase) *
        (currentAmplitude * Real.cos (frequency * t)) =
      voltageAmplitude * currentAmplitude / 2 *
        (Real.cos phase + Real.cos (2 * (frequency * t) + phase)) := by
  have doubled : 2 * (frequency * t) + phase = frequency * t + frequency * t + phase := by ring
  rw [doubled, Real.cos_add (frequency * t + frequency * t) phase,
    Real.cos_add (frequency * t) (frequency * t), Real.sin_add (frequency * t) (frequency * t),
    Real.cos_add (frequency * t) phase]
  have pythagoras := Real.sin_sq_add_cos_sq (frequency * t)
  linear_combination
    (voltageAmplitude * currentAmplitude * Real.cos phase / 2) * pythagoras

/-- In phase, the instantaneous power of a resistive load never becomes negative: a
resistor never returns energy. -/
theorem resistive_instantaneous_nonneg {voltageAmplitude currentAmplitude : ℝ}
    (aligned : 0 ≤ voltageAmplitude * currentAmplitude) (frequency t : ℝ) :
    0 ≤ voltageAmplitude * Real.cos (frequency * t) * (currentAmplitude * Real.cos (frequency * t)) := by
  have square : 0 ≤ Real.cos (frequency * t) * Real.cos (frequency * t) := mul_self_nonneg _
  nlinarith

/-! ## Phasor domain -/

/-- Complex power of an element carrying the phasor current `i` at the phasor voltage
`v`, in amplitude convention: `S = V conj(I) / 2`. -/
noncomputable def complexPower (v i : ℂ) : ℂ := v * (starRingEnd ℂ) i / 2

/-- Real (dissipated) power. -/
noncomputable def realPower (v i : ℂ) : ℝ := (complexPower v i).re

/-- Reactive (exchanged) power. -/
noncomputable def reactivePower (v i : ℂ) : ℝ := (complexPower v i).im

/-- Apparent power, the magnitude of the complex power. -/
noncomputable def apparentPower (v i : ℂ) : ℝ := ‖complexPower v i‖

/-- Ohm's law fixes the complex power of a linear element: it is the impedance scaled by
the squared current magnitude. -/
theorem complexPower_ohm (z i : ℂ) :
    complexPower (z * i) i = z * (Complex.normSq i : ℂ) / 2 := by
  simp only [complexPower]
  rw [mul_assoc, Complex.mul_conj]

theorem realPower_ohm (z i : ℂ) : realPower (z * i) i = z.re * Complex.normSq i / 2 := by
  simp [realPower, complexPower_ohm]

theorem reactivePower_ohm (z i : ℂ) : reactivePower (z * i) i = z.im * Complex.normSq i / 2 := by
  simp [reactivePower, complexPower_ohm]

/-- **The power triangle.** Apparent power is the hypotenuse of the real and reactive
powers, for every pair of terminal phasors. -/
theorem apparent_sq (v i : ℂ) :
    apparentPower v i ^ 2 = realPower v i ^ 2 + reactivePower v i ^ 2 := by
  simp only [apparentPower, realPower, reactivePower]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem realPower_le_apparent (v i : ℂ) : realPower v i ≤ apparentPower v i := by
  have triangle := apparent_sq v i
  have nonneg : 0 ≤ apparentPower v i := norm_nonneg _
  nlinarith [sq_nonneg (reactivePower v i), sq_nonneg (realPower v i - apparentPower v i)]

/-- **A passive impedance dissipates nonnegative power** at every operating point, which
is the phasor form of passivity. -/
theorem realPower_nonneg_of_passive {z : ℂ} (passive : 0 ≤ z.re) (i : ℂ) :
    0 ≤ realPower (z * i) i := by
  rw [realPower_ohm]
  have magnitude : 0 ≤ Complex.normSq i := Complex.normSq_nonneg i
  positivity

/-- **An ideal reactance dissipates nothing.** With no resistive part the real power
vanishes identically, so the element only exchanges energy. -/
theorem realPower_reactance {z : ℂ} (reactive : z.re = 0) (i : ℂ) :
    realPower (z * i) i = 0 := by
  rw [realPower_ohm, reactive, zero_mul, zero_div]

/-- Conversely, an element that dissipates nothing at some nonzero current has no
resistive part: dissipation and resistance determine each other. -/
theorem reactance_of_realPower {z i : ℂ} (flowing : i ≠ 0) (lossless : realPower (z * i) i = 0) :
    z.re = 0 := by
  rw [realPower_ohm] at lossless
  have magnitude : Complex.normSq i ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using flowing
  have product : z.re * Complex.normSq i = 0 := by linarith [lossless]
  rcases mul_eq_zero.mp product with resistive | degenerate
  · exact resistive
  · exact absurd degenerate magnitude

/-- Displacement power factor of an impedance: the cosine of its argument. -/
noncomputable def powerFactor (z : ℂ) : ℝ := z.re / ‖z‖

/-- **The power factor never exceeds unity.** A load cannot dissipate more than its
apparent power. -/
theorem abs_powerFactor_le_one {z : ℂ} (nondegenerate : z ≠ 0) : |powerFactor z| ≤ 1 := by
  have positive : 0 < ‖z‖ := norm_pos_iff.mpr nondegenerate
  have bound : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  rw [powerFactor, abs_div, abs_of_pos positive, div_le_one positive]
  exact bound

/-- The power factor is unity exactly for a purely resistive impedance with positive
resistance, which is the matched condition a power system aims at. -/
theorem powerFactor_eq_one_iff {z : ℂ} (resistive : 0 < z.re) :
    powerFactor z = 1 ↔ z.im = 0 := by
  have nondegenerate : z ≠ 0 := by
    intro degenerate
    rw [degenerate] at resistive
    simp at resistive
  have positive : 0 < ‖z‖ := norm_pos_iff.mpr nondegenerate
  rw [powerFactor, div_eq_one_iff_eq (ne_of_gt positive)]
  constructor
  · intro equal
    have squared : ‖z‖ ^ 2 = z.re ^ 2 := by rw [equal]
    rw [Complex.sq_norm, Complex.normSq_apply] at squared
    nlinarith [squared]
  · intro vanishing
    have squared : ‖z‖ ^ 2 = z.re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, vanishing]
      ring
    nlinarith [norm_nonneg z, resistive, squared]

/-- Real power expressed through the power factor: `P = |V| |I| cos φ / 2`, the form used
in power engineering. It agrees with the average power of `Phasor.averagePower`. -/
theorem realPower_powerFactor {z : ℂ} (nondegenerate : z ≠ 0) (i : ℂ) :
    realPower (z * i) i = ‖z‖ * Complex.normSq i * powerFactor z / 2 := by
  have positive : 0 < ‖z‖ := norm_pos_iff.mpr nondegenerate
  rw [realPower_ohm, powerFactor]
  field_simp

/-- The phasor and the average-power descriptions agree: the real power drawn by an
impedance carrying a current of the given amplitude is the average power already defined
in `Synthesis.Domains.Electronics.Phasor`. -/
theorem realPower_eq_averagePower (z : ℂ) (amplitude : ℝ) :
    realPower (z * (amplitude : ℂ)) (amplitude : ℂ) = Phasor.averagePower z amplitude := by
  rw [realPower_ohm, Phasor.averagePower, Complex.normSq_apply]
  simp
  ring

end Synthesis.Domains.Electronics.Power
