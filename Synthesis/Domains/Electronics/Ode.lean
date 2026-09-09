import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

namespace Synthesis.Domains.Electronics.Ode
set_option autoImplicit false

/-! # Scalar linear ordinary differential equations

Every lumped circuit whose behaviour is a differential relation reduces, in the linear
time-invariant case, to the scalar equation `x' = a x` and to compositions of it. This
module isolates that mathematics so the circuit modules can state their results without
re-proving it: `Transient` uses it for the first-order relaxation and `SecondOrder` uses
it twice, once for each factor of the characteristic polynomial.

The two facts that matter are that the exponential solves the equation and that it is
the *only* solution with a given initial value. Uniqueness is what turns a closed form
from a guess into a model, and it is obtained here in the standard way: the quotient of
a solution by the exponential has zero derivative everywhere, hence is constant.

Nothing in this module is electrical. It carries no operating envelope and no
idealization of its own; the modelling assumptions belong to the circuit modules that
instantiate it. -/

/-- The derivative of a scaled exponential, in the form the circuit modules need: the
rate is the coefficient times the value, so the function is visibly a solution of
`x' = a x`. -/
theorem hasDerivAt_exponential (a c t : ℝ) :
    HasDerivAt (fun s => c * Real.exp (a * s)) (a * (c * Real.exp (a * t))) t := by
  have inner : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have scaled := inner.exp.const_mul c
  have value : c * (Real.exp (a * t) * a) = a * (c * Real.exp (a * t)) := by ring
  rwa [value] at scaled

/-- A trajectory obeys the scalar linear equation `x' = a x` when its derivative is
everywhere the coefficient times its value. Stating the rate as a separate function
avoids assuming differentiability twice. -/
def Linear (a : ℝ) (x rate : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt x (rate t) t) ∧ ∀ t, rate t = a * x t

/-- The scaled exponential is a solution for every initial value. -/
theorem exponential_linear (a c : ℝ) :
    Linear a (fun s => c * Real.exp (a * s)) (fun s => a * (c * Real.exp (a * s))) :=
  ⟨fun t => hasDerivAt_exponential a c t, fun _ => rfl⟩

/-- **Uniqueness of the scalar linear solution.** Every differentiable trajectory obeying
`x' = a x` is the exponential of its own initial value, so the closed form is the
equation's only behaviour. -/
theorem linear_unique {a : ℝ} {x rate : ℝ → ℝ} (solution : Linear a x rate) (t : ℝ) :
    x t = x 0 * Real.exp (a * t) := by
  obtain ⟨differentiable, ode⟩ := solution
  have derivative : ∀ s : ℝ, HasDerivAt (fun y => x y * Real.exp (-a * y)) 0 s := by
    intro s
    have inner : HasDerivAt (fun y : ℝ => -a * y) (-a) s := by
      simpa using (hasDerivAt_id s).const_mul (-a)
    have product := (differentiable s).mul inner.exp
    have vanishes : rate s * Real.exp (-a * s) + x s * (Real.exp (-a * s) * -a) = 0 := by
      rw [ode s]
      ring
    rwa [vanishes] at product
  have constant : x t * Real.exp (-a * t) = x 0 * Real.exp (-a * 0) :=
    is_const_of_deriv_eq_zero (fun y => (derivative y).differentiableAt)
      (fun y => (derivative y).deriv) t 0
  rw [mul_zero, Real.exp_zero, mul_one, neg_mul, Real.exp_neg] at constant
  have positive : (0 : ℝ) < Real.exp (a * t) := Real.exp_pos (a * t)
  have nonzero : Real.exp (a * t) ≠ 0 := ne_of_gt positive
  field_simp at constant
  linear_combination constant

/-- Two solutions of the same scalar linear equation that agree at the origin agree
everywhere. This is the form used to identify a measured trajectory with a model. -/
theorem linear_determined {a : ℝ} {x xrate y yrate : ℝ → ℝ}
    (first : Linear a x xrate) (second : Linear a y yrate) (initial : x 0 = y 0) (t : ℝ) :
    x t = y t := by
  rw [linear_unique first t, linear_unique second t, initial]

/-- A solution that starts at rest stays at rest: the equation has no spontaneous
excitation. -/
theorem linear_zero {a : ℝ} {x rate : ℝ → ℝ} (solution : Linear a x rate)
    (initial : x 0 = 0) (t : ℝ) : x t = 0 := by
  rw [linear_unique solution t, initial, zero_mul]

/-- The solution never changes sign, because the exponential factor is strictly
positive. A first-order relaxation cannot overshoot through zero. -/
theorem linear_sign {a : ℝ} {x rate : ℝ → ℝ} (solution : Linear a x rate)
    (initial : 0 ≤ x 0) (t : ℝ) : 0 ≤ x t := by
  rw [linear_unique solution t]
  exact mul_nonneg initial (le_of_lt (Real.exp_pos _))

/-- Solutions of one linear equation form a vector space: they add. -/
theorem linear_add {a : ℝ} {x xrate y yrate : ℝ → ℝ}
    (first : Linear a x xrate) (second : Linear a y yrate) :
    Linear a (fun t => x t + y t) (fun t => xrate t + yrate t) := by
  refine ⟨fun t => (first.1 t).add (second.1 t), fun t => ?_⟩
  show xrate t + yrate t = a * (x t + y t)
  rw [first.2 t, second.2 t]
  ring

theorem linear_smul {a : ℝ} {x rate : ℝ → ℝ} (solution : Linear a x rate) (c : ℝ) :
    Linear a (fun t => c * x t) (fun t => c * rate t) := by
  refine ⟨fun t => (solution.1 t).const_mul c, fun t => ?_⟩
  show c * rate t = a * (c * x t)
  rw [solution.2 t]
  ring

end Synthesis.Domains.Electronics.Ode
