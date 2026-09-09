import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Synthesis.Domains.Electronics.Digital
set_option autoImplicit false

/-! ## Static logic levels

A voltage represents a Boolean value only through a discipline of thresholds. The
guarantee below is the reason digital logic composes: an output driven to a valid level
is still read correctly after bounded interference. -/

/-- A static logic level discipline: input thresholds and guaranteed output levels. -/
structure Discipline where
  inputLowMax : ℝ
  inputHighMin : ℝ
  outputLowMax : ℝ
  outputHighMin : ℝ
  separated : inputLowMax < inputHighMin
  lowRestoring : outputLowMax ≤ inputLowMax
  highRestoring : inputHighMin ≤ outputHighMin

namespace Discipline

/-- Low-level noise margin. -/
def marginLow (d : Discipline) : ℝ := d.inputLowMax - d.outputLowMax

/-- High-level noise margin. -/
def marginHigh (d : Discipline) : ℝ := d.outputHighMin - d.inputHighMin

theorem marginLow_nonneg (d : Discipline) : 0 ≤ d.marginLow := by
  have := d.lowRestoring
  simp only [marginLow]
  linarith

theorem marginHigh_nonneg (d : Discipline) : 0 ≤ d.marginHigh := by
  have := d.highRestoring
  simp only [marginHigh]
  linarith

/-- Interpretation of a voltage as a Boolean value. Voltages inside the forbidden band
have no interpretation; this is a refusal to guess, not a third logic value. -/
noncomputable def interpret (d : Discipline) (v : ℝ) : Option Bool :=
  if v ≤ d.inputLowMax then some false
  else if d.inputHighMin ≤ v then some true
  else none

/-- No voltage is read as both values: the thresholds are unambiguous. -/
theorem interpret_unambiguous (d : Discipline) (v : ℝ) :
    ¬(d.interpret v = some false ∧ d.interpret v = some true) := by
  rintro ⟨low, high⟩
  rw [low] at high
  exact Bool.false_ne_true (Option.some.inj high)

/-- A voltage in the forbidden band has no interpretation. -/
theorem interpret_forbidden (d : Discipline) {v : ℝ}
    (above : d.inputLowMax < v) (below : v < d.inputHighMin) : d.interpret v = none := by
  simp only [interpret]
  rw [if_neg (not_le.mpr above), if_neg (not_le.mpr below)]

/-- **Level restoration**: a valid driven low is read as `false`. -/
theorem interpret_driven_low (d : Discipline) {v : ℝ} (driven : v ≤ d.outputLowMax) :
    d.interpret v = some false := by
  have := d.lowRestoring
  simp only [interpret]
  rw [if_pos (by linarith)]

/-- **Level restoration**: a valid driven high is read as `true`. -/
theorem interpret_driven_high (d : Discipline) {v : ℝ} (driven : d.outputHighMin ≤ v) :
    d.interpret v = some true := by
  have separation := d.separated
  have restoring := d.highRestoring
  simp only [interpret]
  rw [if_neg (by push Not; linarith), if_pos (by linarith)]

/-- **Noise immunity**: interference bounded by the noise margin cannot change the value
read from a driven low output. -/
theorem noise_immunity_low (d : Discipline) {v noise : ℝ} (driven : v ≤ d.outputLowMax)
    (bounded : |noise| ≤ d.marginLow) : d.interpret (v + noise) = some false := by
  have bound : noise ≤ d.marginLow := le_trans (le_abs_self noise) bounded
  have margin : d.marginLow = d.inputLowMax - d.outputLowMax := rfl
  simp only [interpret]
  rw [if_pos (by rw [margin] at bound; linarith)]

/-- **Noise immunity**: interference bounded by the noise margin cannot change the value
read from a driven high output. -/
theorem noise_immunity_high (d : Discipline) {v noise : ℝ} (driven : d.outputHighMin ≤ v)
    (bounded : |noise| ≤ d.marginHigh) : d.interpret (v + noise) = some true := by
  have bound : -noise ≤ d.marginHigh := le_trans (neg_le_abs noise) bounded
  have margin : d.marginHigh = d.outputHighMin - d.inputHighMin := rfl
  have separation := d.separated
  rw [margin] at bound
  simp only [interpret]
  rw [if_neg (by push Not; linarith), if_pos (by linarith)]

end Discipline
end Synthesis.Domains.Electronics.Digital
