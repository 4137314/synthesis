import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.Storage
set_option autoImplicit false

/-! # Energy storage elements in continuous time

Capacitors and inductors are the first elements of this domain whose behaviour is a
differential relation rather than an algebraic one, so their model is stated over real
time with Mathlib's derivative. Voltages, currents, charges and fluxes are real-valued
functions of time in coherent SI units.

The central results are the energy theorems: the instantaneous power `v i` is exactly
the time derivative of the stored energy, and its integral over an interval is the
energy difference between the endpoints. That is what justifies calling `C v² / 2` and
`L i² / 2` stored energies rather than arbitrary quadratic expressions.

The elements are linear and time invariant: no dielectric loss, leakage, saturation,
hysteresis, temperature dependence or voltage coefficient is modelled. -/

/-- An ideal linear capacitor. Zero capacitance is excluded so that terminal voltage is
determined by stored charge. -/
structure Capacitor where
  capacitance : ℝ
  positive : 0 < capacitance

/-- An ideal linear inductor. Zero inductance is excluded so that branch current is
determined by flux linkage. -/
structure Inductor where
  inductance : ℝ
  positive : 0 < inductance

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

namespace Inductor

/-- Flux linkage at a given branch current. -/
def flux (l : Inductor) (i : ℝ) : ℝ := l.inductance * i

/-- Stored magnetic energy at a given branch current. -/
noncomputable def energy (l : Inductor) (i : ℝ) : ℝ := l.inductance * i ^ 2 / 2

/-- The constitutive law `v = dφ/dt`, Faraday's law for a lumped inductor. -/
def Constitutive (l : Inductor) (i v : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt (fun s => l.flux (i s)) (v t) t

theorem energy_nonneg (l : Inductor) (i : ℝ) : 0 ≤ l.energy i := by
  have := l.positive
  unfold energy
  positivity

theorem energy_flux (l : Inductor) (i : ℝ) :
    2 * l.inductance * l.energy i = l.flux i ^ 2 := by
  simp only [energy, flux]
  ring

/-- An inductor carrying a constant current sustains no terminal voltage. -/
theorem constant_current_no_voltage (l : Inductor) (value : ℝ) (v : ℝ → ℝ)
    (law : l.Constitutive (fun _ => value) v) (t : ℝ) : v t = 0 := by
  have constant : HasDerivAt (fun _ : ℝ => l.flux value) 0 t := hasDerivAt_const t _
  exact (law t).unique constant

theorem voltage_eq_inductance_mul_rate (l : Inductor) (i v : ℝ → ℝ) (t rate : ℝ)
    (law : l.Constitutive i v) (differentiable : HasDerivAt i rate t) :
    v t = l.inductance * rate := by
  have scaled : HasDerivAt (fun s => l.flux (i s)) (l.inductance * rate) t := by
    simpa [flux] using differentiable.const_mul l.inductance
  exact (law t).unique scaled

/-- **Energy theorem for an inductor**: absorbed power is the derivative of the stored
magnetic energy. -/
theorem hasDerivAt_energy (l : Inductor) (i v : ℝ → ℝ) (t rate : ℝ)
    (law : l.Constitutive i v) (differentiable : HasDerivAt i rate t) :
    HasDerivAt (fun s => l.energy (i s)) (v t * i t) t := by
  have square : HasDerivAt (fun s => i s ^ 2) (rate * i t + i t * rate) t := by
    have product := differentiable.mul differentiable
    have squared : (i * i : ℝ → ℝ) = fun s => i s ^ 2 := by
      funext s
      simp only [Pi.mul_apply]
      ring
    rwa [squared] at product
  have scaled := (square.const_mul l.inductance).div_const 2
  have voltage := voltage_eq_inductance_mul_rate l i v t rate law differentiable
  have value : l.inductance * (rate * i t + i t * rate) / 2 = v t * i t := by
    rw [voltage]
    ring
  rw [value] at scaled
  exact scaled

theorem energy_integral (l : Inductor) (i v : ℝ → ℝ) (rate : ℝ → ℝ) (a b : ℝ)
    (law : l.Constitutive i v) (differentiable : ∀ t, HasDerivAt i (rate t) t)
    (integrable : IntervalIntegrable (fun t => v t * i t) MeasureTheory.volume a b) :
    ∫ t in a..b, v t * i t = l.energy (i b) - l.energy (i a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_energy l i v t (rate t) law (differentiable t)) integrable

/-- Inductances add in series: at a common current the terminal voltages sum. -/
def series (a b : Inductor) : Inductor :=
  ⟨a.inductance + b.inductance, by have := a.positive; have := b.positive; linarith⟩

theorem series_constitutive (a b : Inductor) (i va vb : ℝ → ℝ)
    (lawA : a.Constitutive i va) (lawB : b.Constitutive i vb) :
    (series a b).Constitutive i (fun t => va t + vb t) := by
  intro t
  have sum := (lawA t).add (lawB t)
  have combined : (fun s => (series a b).flux (i s)) =
      fun s => a.flux (i s) + b.flux (i s) := by
    funext s
    simp only [flux, series]
    ring
  rw [combined]
  exact sum

theorem series_energy (a b : Inductor) (i : ℝ) :
    (series a b).energy i = a.energy i + b.energy i := by
  simp only [energy, series]
  ring

end Inductor
end Synthesis.Domains.Electronics.Storage
