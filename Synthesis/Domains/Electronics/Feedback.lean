import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace Synthesis.Domains.Electronics.Feedback
set_option autoImplicit false

/-! # Negative feedback and operational amplifier configurations

A memoryless negative feedback loop with forward gain `A` and feedback fraction `β` has
closed-loop gain `A / (1 + A β)`. This module proves the standard consequences: gain
reduction, desensitization to the forward gain, and convergence to `1 / β` as the
forward gain grows.

The two classical operational amplifier configurations are then *derived* from the
finite-gain device equation together with the input node equation, not postulated: the
inverting and non-inverting closed forms follow, and the ideal gains are their limits
as the open-loop gain diverges.

Everything here is static. Frequency response, slew rate, offset, noise, saturation and
loop stability are not modelled, and no theorem below implies that a physical loop with
these static parameters is stable. -/

open Filter Topology

/-- Closed-loop gain of a memoryless negative feedback loop. -/
noncomputable def closedLoopGain (forward feedback : ℝ) : ℝ :=
  forward / (1 + forward * feedback)

/-- Loop gain, the quantity that measures how much feedback is applied. -/
def loopGain (forward feedback : ℝ) : ℝ := forward * feedback

theorem closedLoop_positive {forward feedback : ℝ} (amplifying : 0 < forward)
    (fraction : 0 ≤ feedback) : 0 < closedLoopGain forward feedback := by
  have loop : 0 < 1 + forward * feedback := by positivity
  exact div_pos amplifying loop

/-- Feedback trades gain for the properties proved below: the closed loop is never
stronger than the forward path. -/
theorem closedLoop_le_forward {forward feedback : ℝ} (amplifying : 0 < forward)
    (fraction : 0 ≤ feedback) : closedLoopGain forward feedback ≤ forward := by
  have loop : 0 < 1 + forward * feedback := by positivity
  rw [closedLoopGain, div_le_iff₀ loop]
  nlinarith [mul_nonneg (le_of_lt amplifying) (mul_nonneg (le_of_lt amplifying) fraction)]

/-- The closed-loop gain solves its defining equation `G (1 + A β) = A`. -/
theorem closedLoop_equation {forward feedback : ℝ} (loop : 1 + forward * feedback ≠ 0) :
    closedLoopGain forward feedback * (1 + forward * feedback) = forward := by
  rw [closedLoopGain]
  field_simp

/-- **Desensitization**: the relative sensitivity of the closed-loop gain to the forward
gain is `1 / (1 + A β)`, so a large loop gain suppresses forward-gain variation. -/
theorem hasDerivAt_closedLoop {forward feedback : ℝ} (loop : 1 + forward * feedback ≠ 0) :
    HasDerivAt (fun a => closedLoopGain a feedback)
      (1 / (1 + forward * feedback) ^ 2) forward := by
  have denominator : HasDerivAt (fun a : ℝ => 1 + a * feedback) feedback forward := by
    have base : HasDerivAt (fun a : ℝ => a * feedback) feedback forward := by
      have scaled := (hasDerivAt_id' (x := forward)).mul_const feedback
      rw [one_mul] at scaled
      exact scaled
    have sum := (hasDerivAt_const forward (1 : ℝ)).add base
    rw [zero_add] at sum
    exact sum
  have quotient := (hasDerivAt_id' (x := forward)).div denominator loop
  have value : (1 * (1 + forward * feedback) - forward * feedback) /
      (1 + forward * feedback) ^ 2 = 1 / (1 + forward * feedback) ^ 2 := by
    congr 1
    ring
  rw [value] at quotient
  exact quotient

theorem sensitivity_relative {forward feedback : ℝ} (amplifying : 0 < forward)
    (fraction : 0 ≤ feedback) :
    1 / (1 + forward * feedback) ^ 2 * forward / closedLoopGain forward feedback =
      1 / (1 + forward * feedback) := by
  have loop : 0 < 1 + forward * feedback := by positivity
  have nonzero : forward ≠ 0 := ne_of_gt amplifying
  simp only [closedLoopGain]
  field_simp

/-- With a large forward gain the closed-loop gain approaches `1 / β`, which depends
only on the feedback network. -/
theorem closedLoop_tendsto {feedback : ℝ} (fraction : 0 < feedback) :
    Tendsto (fun a => closedLoopGain a feedback) atTop (𝓝 (1 / feedback)) := by
  have rewritten : (fun a : ℝ => 1 / (1 / a + feedback)) =ᶠ[atTop]
      fun a : ℝ => closedLoopGain a feedback := by
    filter_upwards [eventually_gt_atTop 0] with a positive
    have nonzero : a ≠ 0 := ne_of_gt positive
    have loop : 1 + a * feedback ≠ 0 := by positivity
    have inner : 1 / a + feedback ≠ 0 := by positivity
    rw [closedLoopGain, div_eq_div_iff inner loop]
    field_simp
  have inner : Tendsto (fun a : ℝ => 1 / a + feedback) atTop (𝓝 (0 + feedback)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
  rw [zero_add] at inner
  have quotient : Tendsto (fun a : ℝ => 1 / (1 / a + feedback)) atTop (𝓝 (1 / feedback)) :=
    tendsto_const_nhds.div inner (ne_of_gt fraction)
  exact quotient.congr' rewritten

/-- An operational amplifier modelled by a finite differential gain. -/
structure OpAmp where
  gain : ℝ
  positive : 0 < gain

namespace OpAmp

/-- **Inverting amplifier, finite gain.** The device equation and the input node
equation determine the output uniquely. -/
theorem inverting_closed_form (amp : OpAmp) {input feedbackResistance inputVoltage
    invertingInput output : ℝ}
    (device : output = amp.gain * (0 - invertingInput))
    (node : (inputVoltage - invertingInput) / input = (invertingInput - output) / feedbackResistance)
    (inputNonzero : input ≠ 0) (feedbackNonzero : feedbackResistance ≠ 0)
    (loop : feedbackResistance + input * (1 + amp.gain) ≠ 0) :
    output = -(amp.gain * feedbackResistance * inputVoltage) /
      (feedbackResistance + input * (1 + amp.gain)) := by
  have deviceProduct : amp.gain * invertingInput = -output := by
    rw [device]
    ring
  rw [div_eq_div_iff inputNonzero feedbackNonzero] at node
  rw [eq_div_iff loop]
  linear_combination amp.gain * node + (feedbackResistance + input) * deviceProduct

/-- The ideal inverting gain `-R_f / R_in` is the large-gain limit of the closed form. -/
theorem inverting_ideal_limit {input feedbackResistance inputVoltage : ℝ}
    (inputPositive : 0 < input) (feedbackPositive : 0 < feedbackResistance) :
    Tendsto (fun a : ℝ => -(a * feedbackResistance * inputVoltage) /
        (feedbackResistance + input * (1 + a))) atTop
      (𝓝 (-(feedbackResistance / input) * inputVoltage)) := by
  have rewritten : (fun a : ℝ => -(feedbackResistance * inputVoltage) /
      ((feedbackResistance + input) / a + input)) =ᶠ[atTop]
      fun a : ℝ => -(a * feedbackResistance * inputVoltage) /
        (feedbackResistance + input * (1 + a)) := by
    filter_upwards [eventually_gt_atTop 0] with a positive
    have nonzero : a ≠ 0 := ne_of_gt positive
    have denominator : feedbackResistance + input * (1 + a) ≠ 0 := by positivity
    have scaled : (feedbackResistance + input) / a + input ≠ 0 := by positivity
    rw [div_eq_div_iff scaled denominator]
    field_simp
    ring
  have inner : Tendsto (fun a : ℝ => (feedbackResistance + input) / a + input) atTop
      (𝓝 (0 + input)) := (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
  rw [zero_add] at inner
  have quotient : Tendsto (fun a : ℝ => -(feedbackResistance * inputVoltage) /
      ((feedbackResistance + input) / a + input)) atTop
      (𝓝 (-(feedbackResistance * inputVoltage) / input)) :=
    tendsto_const_nhds.div inner (ne_of_gt inputPositive)
  have value : -(feedbackResistance * inputVoltage) / input =
      -(feedbackResistance / input) * inputVoltage := by
    field_simp
  rw [value] at quotient
  exact quotient.congr' rewritten

/-- **Non-inverting amplifier, ideal constraints.** With a virtual short and no input
current the closed-loop gain is `1 + R_f / R_in`. -/
theorem non_inverting_ideal {input feedbackResistance inputVoltage invertingInput output : ℝ}
    (virtualShort : invertingInput = inputVoltage)
    (divider : invertingInput = output * input / (input + feedbackResistance))
    (inputNonzero : input ≠ 0) (loop : input + feedbackResistance ≠ 0) :
    output = (1 + feedbackResistance / input) * inputVoltage := by
  rw [virtualShort, eq_div_iff loop] at divider
  field_simp
  linear_combination -divider

/-- A unity-gain buffer follows its input exactly under the ideal constraints. -/
theorem buffer_ideal {inputVoltage invertingInput output : ℝ}
    (virtualShort : invertingInput = inputVoltage) (feedback : invertingInput = output) :
    output = inputVoltage := by
  rw [← feedback, virtualShort]

end OpAmp
end Synthesis.Domains.Electronics.Feedback
