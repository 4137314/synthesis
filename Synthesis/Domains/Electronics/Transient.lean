import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Synthesis.Domains.Electronics.Storage

namespace Synthesis.Domains.Electronics.Transient
set_option autoImplicit false

/-! # First-order transients

A single storage element with a single resistance obeys `τ x' + x = x_∞`, with the time
constant `τ = R C` for a capacitor and `τ = L / R` for an inductor. This module gives
the closed-form solution, proves that it solves the equation, and proves that it is the
*only* solution with the given initial value.

Uniqueness is what makes the closed form a model rather than a guess: it is obtained by
showing that `x(t) e^{t/τ}` has zero derivative, hence is constant. Nothing here assumes
a particular circuit topology; `rcConstitutive` connects the solution to the element
laws of `Synthesis.Domains.Electronics.Storage`. -/

open Filter Topology

/-- A first-order relaxation with a strictly positive time constant. Zero time constant
would describe an instantaneous, unphysical transition and is excluded. -/
structure FirstOrder where
  timeConstant : ℝ
  positive : 0 < timeConstant

namespace FirstOrder

/-- Time constant of a resistor-capacitor pair. -/
noncomputable def ofRC {r c : ℝ} (resistance : 0 < r) (capacitance : 0 < c) : FirstOrder :=
  ⟨r * c, mul_pos resistance capacitance⟩

/-- Time constant of a resistor-inductor pair. -/
noncomputable def ofRL {r l : ℝ} (resistance : 0 < r) (inductance : 0 < l) : FirstOrder :=
  ⟨l / r, div_pos inductance resistance⟩

/-- Source-free (natural) response with the given initial value. -/
noncomputable def natural (f : FirstOrder) (initial t : ℝ) : ℝ :=
  initial * Real.exp (-t / f.timeConstant)

/-- Step response relaxing from `initial` towards the forced value `final`. -/
noncomputable def step (f : FirstOrder) (initial final t : ℝ) : ℝ :=
  final + (initial - final) * Real.exp (-t / f.timeConstant)

theorem natural_zero (f : FirstOrder) (initial : ℝ) : f.natural initial 0 = initial := by
  simp [natural]

theorem step_zero (f : FirstOrder) (initial final : ℝ) : f.step initial final 0 = initial := by
  simp [step]

theorem step_natural (f : FirstOrder) (initial final t : ℝ) :
    f.step initial final t = final + f.natural (initial - final) t := by
  simp [step, natural]

/-- After one time constant the natural response has fallen to `e⁻¹` of its start. -/
theorem natural_time_constant (f : FirstOrder) (initial : ℝ) :
    f.natural initial f.timeConstant = initial * Real.exp (-1) := by
  have nonzero : f.timeConstant ≠ 0 := ne_of_gt f.positive
  simp only [natural]
  rw [neg_div, div_self nonzero]

/-- The natural response is differentiable with the derivative required by the model. -/
theorem hasDerivAt_natural (f : FirstOrder) (initial t : ℝ) :
    HasDerivAt (f.natural initial) (-(f.natural initial t) / f.timeConstant) t := by
  have nonzero : f.timeConstant ≠ 0 := ne_of_gt f.positive
  have inner : HasDerivAt (fun s : ℝ => -s / f.timeConstant) (-1 / f.timeConstant) t := by
    simpa using ((hasDerivAt_id t).neg).div_const f.timeConstant
  have exponential := inner.exp
  have scaled := exponential.const_mul initial
  have value : initial * (Real.exp (-t / f.timeConstant) * (-1 / f.timeConstant)) =
      -(f.natural initial t) / f.timeConstant := by
    simp only [natural]
    field_simp
  rw [value] at scaled
  exact scaled

/-- **The natural response solves the first-order equation** `τ x' + x = 0`. -/
theorem natural_ode (f : FirstOrder) (initial t : ℝ) :
    f.timeConstant * (-(f.natural initial t) / f.timeConstant) + f.natural initial t = 0 := by
  have nonzero : f.timeConstant ≠ 0 := ne_of_gt f.positive
  field_simp
  ring

/-- **Uniqueness of the first-order solution.** Every differentiable trajectory obeying
`τ x' + x = 0` is the natural response of its own initial value, so the closed form is
the model's only behaviour. -/
theorem natural_unique (f : FirstOrder) (x rate : ℝ → ℝ)
    (differentiable : ∀ t, HasDerivAt x (rate t) t)
    (ode : ∀ t, f.timeConstant * rate t + x t = 0) (t : ℝ) :
    x t = f.natural (x 0) t := by
  have nonzero : f.timeConstant ≠ 0 := ne_of_gt f.positive
  have derivative : ∀ s : ℝ,
      HasDerivAt (fun y => x y * Real.exp (y / f.timeConstant)) 0 s := by
    intro s
    have inner : HasDerivAt (fun y : ℝ => y / f.timeConstant) (1 / f.timeConstant) s := by
      simpa using (hasDerivAt_id s).div_const f.timeConstant
    have product := (differentiable s).mul inner.exp
    have vanishes : rate s * Real.exp (s / f.timeConstant) +
        x s * (Real.exp (s / f.timeConstant) * (1 / f.timeConstant)) = 0 := by
      have law := ode s
      field_simp
      linear_combination Real.exp (s / f.timeConstant) * law
    rw [vanishes] at product
    exact product
  have constant : x t * Real.exp (t / f.timeConstant) = x 0 * Real.exp (0 / f.timeConstant) :=
    is_const_of_deriv_eq_zero (fun y => (derivative y).differentiableAt)
      (fun y => (derivative y).deriv) t 0
  rw [zero_div, Real.exp_zero, mul_one] at constant
  have positive := Real.exp_pos (t / f.timeConstant)
  simp only [natural, neg_div, Real.exp_neg]
  field_simp
  linarith [constant]

/-- The step response solves the forced equation `τ x' + x = x_∞`. -/
theorem hasDerivAt_step (f : FirstOrder) (initial final t : ℝ) :
    HasDerivAt (f.step initial final)
      (-(f.step initial final t - final) / f.timeConstant) t := by
  have shifted := hasDerivAt_natural f (initial - final) t
  have translated := shifted.const_add final
  have value : -(f.natural (initial - final) t) / f.timeConstant =
      -(f.step initial final t - final) / f.timeConstant := by
    rw [step_natural]
    ring_nf
  rw [value] at translated
  have functions : (fun s => final + f.natural (initial - final) s) = f.step initial final := by
    funext s
    rw [step_natural]
  rwa [functions] at translated

/-- The natural response decays monotonically from a nonnegative start. -/
theorem natural_antitone (f : FirstOrder) {initial : ℝ} (nonneg : 0 ≤ initial) :
    Antitone (f.natural initial) := by
  intro a b hab
  simp only [natural]
  refine mul_le_mul_of_nonneg_left ?_ nonneg
  rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff]
  gcongr
  exact le_of_lt f.positive

/-- The natural response never changes sign and never exceeds its initial magnitude. -/
theorem natural_bounded (f : FirstOrder) {initial t : ℝ} (nonneg : 0 ≤ initial)
    (future : 0 ≤ t) : 0 ≤ f.natural initial t ∧ f.natural initial t ≤ initial := by
  constructor
  · exact mul_nonneg nonneg (le_of_lt (Real.exp_pos _))
  · calc f.natural initial t ≤ f.natural initial 0 :=
        natural_antitone f nonneg future
    _ = initial := natural_zero f initial

/-- The transient dies out: the natural response converges to zero. -/
theorem natural_tendsto_zero (f : FirstOrder) (initial : ℝ) :
    Tendsto (f.natural initial) atTop (𝓝 0) := by
  have base : Tendsto (fun t : ℝ => t / f.timeConstant) atTop atTop :=
    tendsto_id.atTop_div_const f.positive
  have negated : Tendsto (fun t : ℝ => -t / f.timeConstant) atTop atBot := by
    simp only [neg_div]
    exact tendsto_neg_atTop_atBot.comp base
  have exponential : Tendsto (fun t : ℝ => Real.exp (-t / f.timeConstant)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp negated
  have scaled := exponential.const_mul initial
  rw [mul_zero] at scaled
  have functions : (fun t : ℝ => initial * Real.exp (-t / f.timeConstant)) = f.natural initial :=
    rfl
  rwa [functions] at scaled

/-- The step response converges to its forced value. -/
theorem step_tendsto_final (f : FirstOrder) (initial final : ℝ) :
    Tendsto (f.step initial final) atTop (𝓝 final) := by
  have transient := natural_tendsto_zero f (initial - final)
  have shifted := transient.const_add final
  rw [add_zero] at shifted
  have functions : (fun t : ℝ => final + f.natural (initial - final) t) = f.step initial final := by
    funext t
    rw [step_natural]
  rwa [functions] at shifted

end FirstOrder

/-- The natural response of an `RC` pair satisfies the capacitor constitutive law when
the branch current is the resistor current `-v / R`. This links the closed form to the
element models rather than assuming the circuit equation. -/
theorem rcConstitutive {r : ℝ} (resistance : 0 < r) (c : Storage.Capacitor) (initial : ℝ) :
    c.Constitutive ((FirstOrder.ofRC resistance c.positive).natural initial)
      (fun t => -((FirstOrder.ofRC resistance c.positive).natural initial t) / r) := by
  intro t
  set f := FirstOrder.ofRC resistance c.positive with hf
  have nonzero : r ≠ 0 := ne_of_gt resistance
  have capacitance : c.capacitance ≠ 0 := ne_of_gt c.positive
  have derivative := FirstOrder.hasDerivAt_natural f initial t
  have scaled := derivative.const_mul c.capacitance
  have value : c.capacitance * (-(f.natural initial t) / f.timeConstant) =
      -(f.natural initial t) / r := by
    rw [hf]
    simp only [FirstOrder.ofRC]
    field_simp
  rw [value] at scaled
  exact scaled

end Synthesis.Domains.Electronics.Transient
