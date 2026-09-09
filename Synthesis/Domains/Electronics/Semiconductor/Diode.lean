import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Synthesis.Domains.Electronics.Semiconductor
set_option autoImplicit false

/-! # The Shockley diode equation

A static, isothermal large-signal model of a pn junction: `I = I_s (exp (V / n V_T) - 1)`
in coherent SI units.

What is proved here is the mathematics of that equation: strict monotonicity, sign
agreement between terminal voltage and current (hence passivity), the reverse
saturation bound, invertibility on the reachable current range and the small-signal
conductance. Whether a fabricated diode follows the equation, over what range and at
what temperature, remains an engineering premise. Breakdown, high-injection, series
resistance, junction capacitance, recombination and every dynamic effect are outside
this model. -/

/-- Shockley diode parameters: saturation current and the effective thermal voltage
`n V_T`, both strictly positive. -/
structure Diode where
  saturationCurrent : ℝ
  thermalVoltage : ℝ
  saturationPositive : 0 < saturationCurrent
  thermalPositive : 0 < thermalVoltage

namespace Diode

/-- The Shockley equation `I = I_s (exp (V / n V_T) - 1)`. -/
noncomputable def current (d : Diode) (v : ℝ) : ℝ :=
  d.saturationCurrent * (Real.exp (v / d.thermalVoltage) - 1)

/-- Inverse of the Shockley equation on its range. -/
noncomputable def voltage (d : Diode) (i : ℝ) : ℝ :=
  d.thermalVoltage * Real.log (1 + i / d.saturationCurrent)

theorem current_zero (d : Diode) : d.current 0 = 0 := by
  simp [current]

/-- The diode characteristic is strictly increasing, so its operating point is unique
for a given terminal voltage. -/
theorem current_strictMono (d : Diode) : StrictMono d.current := by
  intro a b hab
  have scaled : a / d.thermalVoltage < b / d.thermalVoltage := by
    gcongr
    exact d.thermalPositive
  have exponential := Real.exp_lt_exp.mpr scaled
  have positive := d.saturationPositive
  simp only [current]
  nlinarith

theorem current_injective (d : Diode) : Function.Injective d.current :=
  d.current_strictMono.injective

theorem current_pos_iff (d : Diode) (v : ℝ) : 0 < d.current v ↔ 0 < v := by
  constructor
  · intro h
    by_contra nonpositive
    have ordered : v ≤ 0 := not_lt.mp nonpositive
    rcases eq_or_lt_of_le ordered with equal | negative
    · rw [equal, current_zero] at h
      exact lt_irrefl 0 h
    · have := d.current_strictMono negative
      rw [current_zero] at this
      linarith
  · intro h
    have := d.current_strictMono h
    rwa [current_zero] at this

/-- **Passivity of the ideal diode**: terminal voltage and current never have opposite
signs, so the device absorbs nonnegative power at every operating point. -/
theorem passive (d : Diode) (v : ℝ) : 0 ≤ v * d.current v := by
  rcases lt_trichotomy v 0 with negative | zero | positive
  · have := d.current_strictMono negative
    rw [current_zero] at this
    nlinarith
  · simp [zero, current_zero]
  · have := d.current_strictMono positive
    rw [current_zero] at this
    nlinarith

/-- Reverse bias saturates: the current can never fall below `-I_s`. -/
theorem reverse_saturation (d : Diode) (v : ℝ) : -d.saturationCurrent < d.current v := by
  have exponential := Real.exp_pos (v / d.thermalVoltage)
  have positive := d.saturationPositive
  simp only [current]
  nlinarith

/-- The voltage inverse is correct on the physically reachable current range. -/
theorem current_voltage (d : Diode) {i : ℝ} (reachable : -d.saturationCurrent < i) :
    d.current (d.voltage i) = i := by
  have saturation : d.saturationCurrent ≠ 0 := ne_of_gt d.saturationPositive
  have thermal : d.thermalVoltage ≠ 0 := ne_of_gt d.thermalPositive
  have argument : 0 < 1 + i / d.saturationCurrent := by
    have positive := d.saturationPositive
    have ratio : -1 < i / d.saturationCurrent := by
      rw [lt_div_iff₀ positive]
      linarith
    linarith
  simp only [current, voltage]
  rw [mul_comm d.thermalVoltage, mul_div_assoc, div_self thermal, mul_one,
    Real.exp_log argument]
  field_simp
  ring

/-- Small-signal conductance: the diode is differentiable and its slope is positive. -/
theorem hasDerivAt_current (d : Diode) (v : ℝ) :
    HasDerivAt d.current
      (d.saturationCurrent / d.thermalVoltage * Real.exp (v / d.thermalVoltage)) v := by
  have thermal : d.thermalVoltage ≠ 0 := ne_of_gt d.thermalPositive
  have inner : HasDerivAt (fun x : ℝ => x / d.thermalVoltage) (1 / d.thermalVoltage) v := by
    simpa using (hasDerivAt_id v).div_const d.thermalVoltage
  have exponential := inner.exp
  have shifted := exponential.sub_const 1
  have scaled := shifted.const_mul d.saturationCurrent
  have value : d.saturationCurrent * (Real.exp (v / d.thermalVoltage) * (1 / d.thermalVoltage)) =
      d.saturationCurrent / d.thermalVoltage * Real.exp (v / d.thermalVoltage) := by
    field_simp
  rw [value] at scaled
  exact scaled

theorem conductance_positive (d : Diode) (v : ℝ) :
    0 < d.saturationCurrent / d.thermalVoltage * Real.exp (v / d.thermalVoltage) := by
  have saturation := d.saturationPositive
  have thermal := d.thermalPositive
  positivity

/-- The classical small-signal identity `g = (I + I_s) / n V_T`: the incremental
conductance is set by the operating-point current. -/
theorem conductance_operating_point (d : Diode) (v : ℝ) :
    d.saturationCurrent / d.thermalVoltage * Real.exp (v / d.thermalVoltage) =
      (d.current v + d.saturationCurrent) / d.thermalVoltage := by
  simp only [current]
  field_simp
  ring

end Diode
end Synthesis.Domains.Electronics.Semiconductor
