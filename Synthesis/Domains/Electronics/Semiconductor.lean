import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Synthesis.Domains.Electronics.Semiconductor
set_option autoImplicit false

/-! # Nonlinear device models

Two standard large-signal models: the Shockley diode equation and the square-law
long-channel field-effect transistor. Both are static, isothermal, single-device models
in coherent SI units.

What is proved here is the mathematics of those equations: monotonicity, sign
agreement between terminal voltage and current, invertibility, the continuity of the
piecewise transistor model at pinch-off, and the small-signal derivatives. Whether a
particular fabricated device follows either equation, over what range, and at what
temperature, remains an engineering premise. Breakdown, high-injection, series
resistance, channel-length modulation, velocity saturation, self-heating and every
dynamic effect are outside these models. -/

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

/-- Square-law long-channel field-effect transistor parameters. -/
structure Mosfet where
  transconductance : ℝ
  threshold : ℝ
  transconductancePositive : 0 < transconductance

namespace Mosfet

/-- Overdrive (gate-source voltage above threshold). -/
def overdrive (m : Mosfet) (gateSource : ℝ) : ℝ := gateSource - m.threshold

/-- Drain current in saturation, `k (V_GS - V_th)² / 2`. Valid while the device is on
and `V_DS ≥ V_GS - V_th`; the hypothesis is the caller's obligation. -/
noncomputable def saturationCurrent (m : Mosfet) (gateSource : ℝ) : ℝ :=
  m.transconductance * m.overdrive gateSource ^ 2 / 2

/-- Drain current in the triode region, `k ((V_GS - V_th) V_DS - V_DS² / 2)`. -/
noncomputable def triodeCurrent (m : Mosfet) (gateSource drainSource : ℝ) : ℝ :=
  m.transconductance * (m.overdrive gateSource * drainSource - drainSource ^ 2 / 2)

theorem saturation_nonneg (m : Mosfet) (gateSource : ℝ) : 0 ≤ m.saturationCurrent gateSource := by
  have := m.transconductancePositive
  unfold saturationCurrent
  positivity

/-- At threshold the device is cut off. -/
theorem cutoff (m : Mosfet) : m.saturationCurrent m.threshold = 0 := by
  simp [saturationCurrent, overdrive]

/-- **Continuity at pinch-off**: the triode and saturation branches agree exactly on the
boundary `V_DS = V_GS - V_th`, so the piecewise model has no jump. -/
theorem pinch_off_continuous (m : Mosfet) (gateSource : ℝ) :
    m.triodeCurrent gateSource (m.overdrive gateSource) = m.saturationCurrent gateSource := by
  simp only [triodeCurrent, saturationCurrent]
  ring

/-- Above threshold the saturation current increases strictly with the gate voltage. -/
theorem saturation_strictMonoOn (m : Mosfet) {a b : ℝ} (onA : m.threshold ≤ a) (ordered : a < b) :
    m.saturationCurrent a < m.saturationCurrent b := by
  have positive := m.transconductancePositive
  have overdriveA : 0 ≤ m.overdrive a := by
    simp only [overdrive]
    linarith
  have overdriveB : m.overdrive a < m.overdrive b := by
    simp only [overdrive]
    linarith
  simp only [saturationCurrent]
  have squares : m.overdrive a ^ 2 < m.overdrive b ^ 2 := by nlinarith
  nlinarith

/-- Transconductance of the saturated device: `g_m = k (V_GS - V_th)`. -/
theorem hasDerivAt_saturation (m : Mosfet) (gateSource : ℝ) :
    HasDerivAt m.saturationCurrent (m.transconductance * m.overdrive gateSource) gateSource := by
  have base : HasDerivAt (fun x : ℝ => m.overdrive x) 1 gateSource := by
    simpa [overdrive] using (hasDerivAt_id gateSource).sub_const m.threshold
  have square : HasDerivAt (fun x : ℝ => m.overdrive x ^ 2)
      (1 * m.overdrive gateSource + m.overdrive gateSource * 1) gateSource := by
    have product := base.mul base
    have squared : ((fun x : ℝ => m.overdrive x) * fun x : ℝ => m.overdrive x) =
        fun x : ℝ => m.overdrive x ^ 2 := by
      funext x
      simp only [Pi.mul_apply]
      ring
    rwa [squared] at product
  have scaled := (square.const_mul m.transconductance).div_const 2
  have value : m.transconductance * (1 * m.overdrive gateSource + m.overdrive gateSource * 1) / 2 =
      m.transconductance * m.overdrive gateSource := by
    ring
  rw [value] at scaled
  exact scaled

/-- **The square-law transconductance relation** `g_m² = 2 k I_D`, the identity used to
size a saturated device from its bias current. -/
theorem transconductance_squared (m : Mosfet) (gateSource : ℝ) :
    (m.transconductance * m.overdrive gateSource) ^ 2 =
      2 * m.transconductance * m.saturationCurrent gateSource := by
  simp only [saturationCurrent]
  ring

/-- Near the origin the triode branch behaves as a linear resistance controlled by the
overdrive: its slope in `V_DS` at zero is the channel conductance `k (V_GS - V_th)`. -/
theorem hasDerivAt_triode (m : Mosfet) (gateSource drainSource : ℝ) :
    HasDerivAt (m.triodeCurrent gateSource)
      (m.transconductance * (m.overdrive gateSource - drainSource)) drainSource := by
  have linear : HasDerivAt (fun x : ℝ => m.overdrive gateSource * x)
      (m.overdrive gateSource) drainSource := by
    simpa using (hasDerivAt_id drainSource).const_mul (m.overdrive gateSource)
  have square : HasDerivAt (fun x : ℝ => x ^ 2) (1 * drainSource + drainSource * 1) drainSource := by
    have product := (hasDerivAt_id drainSource).mul (hasDerivAt_id drainSource)
    have squared : ((id : ℝ → ℝ) * id) = fun x : ℝ => x ^ 2 := by
      funext x
      simp only [Pi.mul_apply, id]
      ring
    rwa [squared] at product
  have combined := linear.sub (square.div_const 2)
  have scaled := combined.const_mul m.transconductance
  have value : m.transconductance *
      (m.overdrive gateSource - (1 * drainSource + drainSource * 1) / 2) =
      m.transconductance * (m.overdrive gateSource - drainSource) := by
    ring
  rw [value] at scaled
  exact scaled

theorem channel_conductance (m : Mosfet) (gateSource : ℝ) :
    HasDerivAt (m.triodeCurrent gateSource)
      (m.transconductance * m.overdrive gateSource) 0 := by
  have derivative := hasDerivAt_triode m gateSource 0
  simpa using derivative

end Mosfet
end Synthesis.Domains.Electronics.Semiconductor
