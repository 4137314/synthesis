import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

namespace Synthesis.Domains.Electronics.Phasor
set_option autoImplicit false

/-! # Sinusoidal steady state

At a fixed angular frequency a linear time-invariant element is described by a complex
impedance. This module defines the impedances of the three passive elements, their
series and parallel combinations, and the series resonant circuit.

The phasor model is a steady-state description: it presupposes a single angular
frequency, linearity and that transients have decayed. It says nothing about start-up,
large-signal behaviour or distortion, and it must not be applied to a nonlinear element.
The time-domain reading of a phasor is fixed by `phasor_time_domain`. -/

open Complex

/-- Impedance of an ideal resistor: purely real and frequency independent. -/
def resistor (r : ℝ) : ℂ := (r : ℂ)

/-- Impedance of an ideal inductor at angular frequency `ω`. -/
noncomputable def inductor (l frequency : ℝ) : ℂ := Complex.I * ((frequency * l : ℝ) : ℂ)

/-- Impedance of an ideal capacitor at angular frequency `ω`. -/
noncomputable def capacitor (c frequency : ℝ) : ℂ := -Complex.I * ((1 / (frequency * c) : ℝ) : ℂ)

/-- Series combination of impedances. -/
def seriesImpedance (a b : ℂ) : ℂ := a + b

/-- Parallel combination of impedances. -/
noncomputable def parallelImpedance (a b : ℂ) : ℂ := a * b / (a + b)

theorem resistor_re (r : ℝ) : (resistor r).re = r := by simp [resistor]

theorem resistor_im (r : ℝ) : (resistor r).im = 0 := by simp [resistor]

/-- An ideal inductor is a pure reactance: it has no resistive part. -/
theorem inductor_re (l frequency : ℝ) : (inductor l frequency).re = 0 := by
  simp [inductor]

theorem inductor_im (l frequency : ℝ) : (inductor l frequency).im = frequency * l := by
  simp [inductor]

theorem capacitor_re (c frequency : ℝ) : (capacitor c frequency).re = 0 := by
  simp [capacitor]

theorem capacitor_im (c frequency : ℝ) :
    (capacitor c frequency).im = -(1 / (frequency * c)) := by
  simp [capacitor]

/-- The capacitive impedance is the reciprocal `1 / (i ω C)` away from the degenerate
zero-frequency and zero-capacitance cases. -/
theorem capacitor_inverse {c frequency : ℝ} (nonzero : frequency * c ≠ 0) :
    capacitor c frequency = 1 / (Complex.I * ((frequency * c : ℝ) : ℂ)) := by
  have cast : ((frequency * c : ℝ) : ℂ) ≠ 0 := by
    simpa using nonzero
  have product : Complex.I * ((frequency * c : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero cast
  have inverse : ((1 / (frequency * c) : ℝ) : ℂ) * ((frequency * c : ℝ) : ℂ) = 1 := by
    push_cast at cast ⊢
    field_simp
    exact div_self cast
  rw [eq_div_iff product, capacitor]
  calc -Complex.I * ((1 / (frequency * c) : ℝ) : ℂ) * (Complex.I * ((frequency * c : ℝ) : ℂ))
      = -(Complex.I * Complex.I) *
        (((1 / (frequency * c) : ℝ) : ℂ) * ((frequency * c : ℝ) : ℂ)) := by ring
    _ = 1 := by rw [Complex.I_mul_I, inverse]; ring

theorem series_impedance_re (a b : ℂ) :
    (seriesImpedance a b).re = a.re + b.re := by simp [seriesImpedance]

theorem series_impedance_comm (a b : ℂ) : seriesImpedance a b = seriesImpedance b a :=
  add_comm a b

theorem series_impedance_assoc (a b c : ℂ) :
    seriesImpedance (seriesImpedance a b) c = seriesImpedance a (seriesImpedance b c) :=
  add_assoc a b c

theorem parallel_impedance_comm (a b : ℂ) : parallelImpedance a b = parallelImpedance b a := by
  simp only [parallelImpedance]
  rw [mul_comm, add_comm]

/-- A series interconnection of passive elements stays passive: resistive parts add and
remain nonnegative. -/
theorem series_passive {a b : ℂ} (ha : 0 ≤ a.re) (hb : 0 ≤ b.re) :
    0 ≤ (seriesImpedance a b).re := by
  rw [series_impedance_re]
  linarith

/-- Average absorbed power of an element carrying a sinusoidal current of the given
amplitude. Only the resistive part of the impedance dissipates. -/
noncomputable def averagePower (z : ℂ) (amplitude : ℝ) : ℝ := amplitude ^ 2 * z.re / 2

theorem average_power_nonneg {z : ℂ} (passive : 0 ≤ z.re) (amplitude : ℝ) :
    0 ≤ averagePower z amplitude := by
  unfold averagePower
  positivity

/-- Ideal reactances absorb no average power: they exchange energy without dissipating. -/
theorem inductor_average_power (l frequency amplitude : ℝ) :
    averagePower (inductor l frequency) amplitude = 0 := by
  simp [averagePower, inductor_re]

theorem capacitor_average_power (c frequency amplitude : ℝ) :
    averagePower (capacitor c frequency) amplitude = 0 := by
  simp [averagePower, capacitor_re]

theorem resistor_average_power (r amplitude : ℝ) :
    averagePower (resistor r) amplitude = amplitude ^ 2 * r / 2 := by
  simp [averagePower, resistor_re]

/-- A phasor denotes the sinusoid recovered by the real part of its rotating form. -/
theorem phasor_time_domain (amplitude phase frequency t : ℝ) :
    ((amplitude : ℂ) * Complex.exp (((frequency * t + phase : ℝ) : ℂ) * Complex.I)).re =
      amplitude * Real.cos (frequency * t + phase) := by
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
end Synthesis.Domains.Electronics.Phasor
