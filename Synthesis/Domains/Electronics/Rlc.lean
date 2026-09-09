import Synthesis.Domains.Electronics.SecondOrder
import Synthesis.Domains.Electronics.Storage

namespace Synthesis.Domains.Electronics.Rlc
set_option autoImplicit false

/-! # Second-order circuits

The two canonical circuits with two storage elements: a series loop and a parallel node.
Their governing equations are *derived* here from the element laws of
`Synthesis.Domains.Electronics.Storage` together with one Kirchhoff constraint, and are
not postulated. The derivation is the same in both cases: state the Kirchhoff law as an
identity in time, differentiate it, and eliminate the remaining state variable with the
constitutive law of the second element.

The resulting `SecondOrder.Damped` parameters are division-free functions of the element
values, so no square root enters this module and the regime classification is decided by
`series_discriminant` and `parallel_discriminant` in cleared-denominator form.

The circuits are source free. A driven circuit adds a forcing term, which this module
does not model; nor does it model parasitic resistance of the reactive elements, mutual
coupling between them, or any departure from linearity and time invariance. -/

open Synthesis.Domains.Electronics.SecondOrder

/-- Relaxation parameters of a source-free series resistor-inductor-capacitor loop:
`i'' + (R / L) i' + i / (L C) = 0`. -/
noncomputable def seriesDamped {r : ℝ} (resistance : 0 ≤ r) (l : Storage.Inductor)
    (c : Storage.Capacitor) : Damped where
  dissipation := r / l.inductance
  stiffness := 1 / (l.inductance * c.capacitance)
  dissipationNonneg := div_nonneg resistance (le_of_lt l.positive)
  stiffnessPositive := div_pos one_pos (mul_pos l.positive c.positive)

/-- Relaxation parameters of a source-free parallel resistor-inductor-capacitor node:
`v'' + v' / (R C) + v / (L C) = 0`. -/
noncomputable def parallelDamped {r : ℝ} (resistance : 0 < r) (l : Storage.Inductor)
    (c : Storage.Capacitor) : Damped where
  dissipation := 1 / (r * c.capacitance)
  stiffness := 1 / (l.inductance * c.capacitance)
  dissipationNonneg := le_of_lt (div_pos one_pos (mul_pos resistance c.positive))
  stiffnessPositive := div_pos one_pos (mul_pos l.positive c.positive)

/-- **The series loop equation, derived.** Given Kirchhoff's voltage law around the loop
as an identity in time, and the capacitor constitutive law, the branch current satisfies
the second-order relaxation with the parameters of `seriesDamped`. Nothing about the
circuit equation is assumed beyond the loop law and the two element laws. -/
theorem series_loop_solves {r : ℝ} (resistance : 0 ≤ r) (l : Storage.Inductor)
    (c : Storage.Capacitor) (current rate acceleration capacitorVoltage capacitorRate : ℝ → ℝ)
    (currentDeriv : ∀ t, HasDerivAt current (rate t) t)
    (rateDeriv : ∀ t, HasDerivAt rate (acceleration t) t)
    (capacitorDeriv : ∀ t, HasDerivAt capacitorVoltage (capacitorRate t) t)
    (capacitorLaw : c.Constitutive capacitorVoltage current)
    (kvl : ∀ t, l.inductance * rate t + r * current t + capacitorVoltage t = 0) :
    (seriesDamped resistance l c).Solves current rate acceleration := by
  refine ⟨currentDeriv, rateDeriv, fun t => ?_⟩
  have inductance : l.inductance ≠ 0 := ne_of_gt l.positive
  have capacitance : c.capacitance ≠ 0 := ne_of_gt c.positive
  have charge := Storage.Capacitor.current_eq_capacitance_mul_rate c capacitorVoltage current t
    (capacitorRate t) capacitorLaw (capacitorDeriv t)
  have loop : HasDerivAt
      (fun s => l.inductance * rate s + r * current s + capacitorVoltage s)
      (l.inductance * acceleration t + r * rate t + capacitorRate t) t :=
    (((rateDeriv t).const_mul l.inductance).add ((currentDeriv t).const_mul r)).add
      (capacitorDeriv t)
  have vanishing :
      (fun s => l.inductance * rate s + r * current s + capacitorVoltage s) = fun _ => (0 : ℝ) :=
    funext kvl
  rw [vanishing] at loop
  have differentiated : l.inductance * acceleration t + r * rate t + capacitorRate t = 0 :=
    loop.unique (hasDerivAt_const t 0)
  show acceleration t + r / l.inductance * rate t +
    1 / (l.inductance * c.capacitance) * current t = 0
  field_simp
  linear_combination c.capacitance * differentiated + charge

/-- **The parallel node equation, derived.** The dual statement: Kirchhoff's current law
at the node together with Faraday's law for the inductor forces the second-order
relaxation of the node voltage. -/
theorem parallel_node_solves {r : ℝ} (resistance : 0 < r) (l : Storage.Inductor)
    (c : Storage.Capacitor)
    (voltage rate acceleration inductorCurrent inductorRate : ℝ → ℝ)
    (voltageDeriv : ∀ t, HasDerivAt voltage (rate t) t)
    (rateDeriv : ∀ t, HasDerivAt rate (acceleration t) t)
    (inductorDeriv : ∀ t, HasDerivAt inductorCurrent (inductorRate t) t)
    (inductorLaw : l.Constitutive inductorCurrent voltage)
    (kcl : ∀ t, c.capacitance * rate t + voltage t / r + inductorCurrent t = 0) :
    (parallelDamped resistance l c).Solves voltage rate acceleration := by
  refine ⟨voltageDeriv, rateDeriv, fun t => ?_⟩
  have inductance : l.inductance ≠ 0 := ne_of_gt l.positive
  have capacitance : c.capacitance ≠ 0 := ne_of_gt c.positive
  have nonzero : r ≠ 0 := ne_of_gt resistance
  have faraday := Storage.Inductor.voltage_eq_inductance_mul_rate l inductorCurrent voltage t
    (inductorRate t) inductorLaw (inductorDeriv t)
  have node : HasDerivAt
      (fun s => c.capacitance * rate s + voltage s / r + inductorCurrent s)
      (c.capacitance * acceleration t + rate t / r + inductorRate t) t :=
    (((rateDeriv t).const_mul c.capacitance).add ((voltageDeriv t).div_const r)).add
      (inductorDeriv t)
  have vanishing :
      (fun s => c.capacitance * rate s + voltage s / r + inductorCurrent s) = fun _ => (0 : ℝ) :=
    funext kcl
  rw [vanishing] at node
  have differentiated : c.capacitance * acceleration t + rate t / r + inductorRate t = 0 :=
    node.unique (hasDerivAt_const t 0)
  have cleared : r * (c.capacitance * acceleration t) + rate t + r * inductorRate t = 0 := by
    field_simp at differentiated
    linarith [differentiated]
  show acceleration t + 1 / (r * c.capacitance) * rate t +
    1 / (l.inductance * c.capacitance) * voltage t = 0
  field_simp
  linear_combination l.inductance * cleared + r * faraday

/-! ## Regime classification from element values

The discriminant is stated with its denominator cleared, so the identity holds without a
nondegeneracy hypothesis and the regime follows by sign comparison alone. -/

theorem series_discriminant {r : ℝ} (resistance : 0 ≤ r) (l : Storage.Inductor)
    (c : Storage.Capacitor) :
    (seriesDamped resistance l c).discriminant * (l.inductance ^ 2 * c.capacitance) =
      r ^ 2 * c.capacitance - 4 * l.inductance := by
  have inductance : l.inductance ≠ 0 := ne_of_gt l.positive
  have capacitance : c.capacitance ≠ 0 := ne_of_gt c.positive
  simp only [seriesDamped, Damped.discriminant]
  field_simp

/-- **The series loop is overdamped exactly when `R² C > 4 L`**, which is the design
inequality separating a monotone from a ringing response. -/
theorem series_overdamped_iff {r : ℝ} (resistance : 0 ≤ r) (l : Storage.Inductor)
    (c : Storage.Capacitor) :
    0 < (seriesDamped resistance l c).discriminant ↔ 4 * l.inductance < r ^ 2 * c.capacitance := by
  have scale : 0 < l.inductance ^ 2 * c.capacitance := by
    have := l.positive
    have := c.positive
    positivity
  have identity := series_discriminant resistance l c
  constructor
  · intro positive
    nlinarith [mul_pos positive scale]
  · intro design
    nlinarith [scale]

theorem parallel_discriminant {r : ℝ} (resistance : 0 < r) (l : Storage.Inductor)
    (c : Storage.Capacitor) :
    (parallelDamped resistance l c).discriminant *
        (r ^ 2 * c.capacitance ^ 2 * l.inductance) =
      l.inductance - 4 * r ^ 2 * c.capacitance := by
  have inductance : l.inductance ≠ 0 := ne_of_gt l.positive
  have capacitance : c.capacitance ≠ 0 := ne_of_gt c.positive
  have nonzero : r ≠ 0 := ne_of_gt resistance
  simp only [parallelDamped, Damped.discriminant]
  field_simp

/-- The parallel node is overdamped exactly when `L > 4 R² C`; note that the inequality
runs the other way from the series case, because the resistor now sets the loss by
shunting rather than by opposing the loop current. -/
theorem parallel_overdamped_iff {r : ℝ} (resistance : 0 < r) (l : Storage.Inductor)
    (c : Storage.Capacitor) :
    0 < (parallelDamped resistance l c).discriminant ↔
      4 * r ^ 2 * c.capacitance < l.inductance := by
  have scale : 0 < r ^ 2 * c.capacitance ^ 2 * l.inductance := by
    have := l.positive
    have := c.positive
    positivity
  have identity := parallel_discriminant resistance l c
  constructor
  · intro positive
    nlinarith [mul_pos positive scale]
  · intro design
    nlinarith [scale]

end Synthesis.Domains.Electronics.Rlc
