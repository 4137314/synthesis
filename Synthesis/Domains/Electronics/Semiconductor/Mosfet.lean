import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Synthesis.Domains.Electronics.Semiconductor
set_option autoImplicit false

/-! # The square-law long-channel field-effect transistor

A static, isothermal large-signal model with two regions: saturation
`I_D = k (V_GS - V_th)² / 2` and triode `I_D = k ((V_GS - V_th) V_DS - V_DS² / 2)`.

The substance of the module is that the piecewise model is coherent: the two branches
agree exactly at pinch-off, the saturation current is monotone above threshold, and the
transconductance obeys the sizing identity `g_m² = 2 k I_D`. Channel-length modulation,
velocity saturation, body effect, subthreshold conduction, self-heating and every
dynamic effect are outside the model, and the validity condition of each region is the
caller's obligation. -/

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
