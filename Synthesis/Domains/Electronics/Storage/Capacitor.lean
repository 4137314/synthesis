import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.Storage
set_option autoImplicit false

/-! # The ideal capacitor in continuous time

The capacitor is the first element of this domain whose behaviour is a differential
relation rather than an algebraic one, so its model is stated over real time with
Mathlib's derivative. Voltages, currents and charges are real-valued functions of time
in coherent SI units.

The central result is the energy theorem: the instantaneous absorbed power `v i` is
exactly the time derivative of the stored energy, and its integral over an interval is
the energy difference between the endpoints. That is what justifies calling `C v² / 2` a
stored energy rather than an arbitrary quadratic expression.

The element is linear and time invariant: no dielectric loss, leakage, voltage
coefficient, temperature dependence or ageing is modelled. -/

/-- An ideal linear capacitor. Zero capacitance is excluded so that terminal voltage is
determined by stored charge. -/
structure Capacitor where
  capacitance : ℝ
  positive : 0 < capacitance

namespace Capacitor

/-- Stored charge at a given terminal voltage. -/
def charge (c : Capacitor) (v : ℝ) : ℝ := c.capacitance * v

/-- Stored electrostatic energy at a given terminal voltage. -/
noncomputable def energy (c : Capacitor) (v : ℝ) : ℝ := c.capacitance * v ^ 2 / 2

/-- The constitutive law `i = dq/dt`: the branch current is the rate of change of the
stored charge. This is the definition of the element, not a derived fact. -/
def Constitutive (c : Capacitor) (v i : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt (fun s => c.charge (v s)) (i t) t

theorem energy_nonneg (c : Capacitor) (v : ℝ) : 0 ≤ c.energy v := by
  have := c.positive
  unfold energy
  positivity

theorem energy_eq_zero_iff (c : Capacitor) (v : ℝ) : c.energy v = 0 ↔ v = 0 := by
  have hc := c.positive
  constructor
  · intro h
    by_contra nonzero
    have square : 0 < v ^ 2 := lt_of_le_of_ne (sq_nonneg v) (Ne.symm (pow_ne_zero 2 nonzero))
    have positive : 0 < c.energy v := by
      unfold energy
      positivity
    linarith
  · intro h
    simp [energy, h]

/-- Energy expressed through the stored charge: `2 C W = q²`. -/
theorem energy_charge (c : Capacitor) (v : ℝ) :
    2 * c.capacitance * c.energy v = c.charge v ^ 2 := by
  simp only [energy, charge]
  ring

/-- A capacitor holding a constant voltage carries no current. -/
theorem constant_voltage_no_current (c : Capacitor) (value : ℝ) (i : ℝ → ℝ)
    (law : c.Constitutive (fun _ => value) i) (t : ℝ) : i t = 0 := by
  have constant : HasDerivAt (fun _ : ℝ => c.charge value) 0 t := hasDerivAt_const t _
  exact (law t).unique constant

/-- The current determines the voltage rate: `i = C dv/dt`. -/
theorem current_eq_capacitance_mul_rate (c : Capacitor) (v i : ℝ → ℝ) (t rate : ℝ)
    (law : c.Constitutive v i) (differentiable : HasDerivAt v rate t) :
    i t = c.capacitance * rate := by
  have scaled : HasDerivAt (fun s => c.charge (v s)) (c.capacitance * rate) t := by
    simpa [charge] using differentiable.const_mul c.capacitance
  exact (law t).unique scaled

/-- **Energy theorem for a capacitor**: the instantaneous absorbed power `v i` is the
time derivative of the stored energy. -/
theorem hasDerivAt_energy (c : Capacitor) (v i : ℝ → ℝ) (t rate : ℝ)
    (law : c.Constitutive v i) (differentiable : HasDerivAt v rate t) :
    HasDerivAt (fun s => c.energy (v s)) (v t * i t) t := by
  have square : HasDerivAt (fun s => v s ^ 2) (rate * v t + v t * rate) t := by
    have product := differentiable.mul differentiable
    have squared : (v * v : ℝ → ℝ) = fun s => v s ^ 2 := by
      funext s
      simp only [Pi.mul_apply]
      ring
    rwa [squared] at product
  have scaled := (square.const_mul c.capacitance).div_const 2
  have current := current_eq_capacitance_mul_rate c v i t rate law differentiable
  have value : c.capacitance * (rate * v t + v t * rate) / 2 = v t * i t := by
    rw [current]
    ring
  rw [value] at scaled
  exact scaled

/-- Integral form of the energy theorem: the energy absorbed over an interval is the
change in stored energy. Reactive elements return exactly what they store. -/
theorem energy_integral (c : Capacitor) (v i : ℝ → ℝ) (rate : ℝ → ℝ) (a b : ℝ)
    (law : c.Constitutive v i) (differentiable : ∀ t, HasDerivAt v (rate t) t)
    (integrable : IntervalIntegrable (fun t => v t * i t) MeasureTheory.volume a b) :
    ∫ t in a..b, v t * i t = c.energy (v b) - c.energy (v a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_energy c v i t (rate t) law (differentiable t)) integrable

/-- Charge conservation in integral form: accumulated current is stored charge. -/
theorem charge_integral (c : Capacitor) (v i : ℝ → ℝ) (a b : ℝ) (law : c.Constitutive v i)
    (integrable : IntervalIntegrable i MeasureTheory.volume a b) :
    ∫ t in a..b, i t = c.charge (v b) - c.charge (v a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => law t) integrable

/-- Capacitances add in parallel: the branch currents of two capacitors at a common
voltage sum to the current of their parallel combination. -/
def parallel (a b : Capacitor) : Capacitor :=
  ⟨a.capacitance + b.capacitance, by have := a.positive; have := b.positive; linarith⟩

theorem parallel_constitutive (a b : Capacitor) (v ia ib : ℝ → ℝ)
    (lawA : a.Constitutive v ia) (lawB : b.Constitutive v ib) :
    (parallel a b).Constitutive v (fun t => ia t + ib t) := by
  intro t
  have sum := (lawA t).add (lawB t)
  have combined : (fun s => (parallel a b).charge (v s)) =
      fun s => a.charge (v s) + b.charge (v s) := by
    funext s
    simp only [charge, parallel]
    ring
  rw [combined]
  exact sum

theorem parallel_energy (a b : Capacitor) (v : ℝ) :
    (parallel a b).energy v = a.energy v + b.energy v := by
  simp only [energy, parallel]
  ring

end Capacitor
end Synthesis.Domains.Electronics.Storage
