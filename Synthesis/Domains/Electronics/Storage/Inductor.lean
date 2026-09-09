import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.Storage
set_option autoImplicit false

/-! # The ideal inductor in continuous time

The dual of `Synthesis.Domains.Electronics.Storage.Capacitor`: Faraday's law `v = dφ/dt`
for a lumped winding, with the same energy theorem in magnetic form. Currents, voltages
and flux linkages are real-valued functions of time in coherent SI units.

The element is linear and time invariant: no winding resistance, core loss, saturation
or hysteresis is modelled, and mutual coupling between windings has its own model in
`Synthesis.Domains.Electronics.Magnetics`. -/

/-- An ideal linear inductor. Zero inductance is excluded so that branch current is
determined by flux linkage. -/
structure Inductor where
  inductance : ℝ
  positive : 0 < inductance

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
