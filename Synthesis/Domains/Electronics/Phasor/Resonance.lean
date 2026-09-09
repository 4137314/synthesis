import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Synthesis.Domains.Electronics.Phasor.Impedance

namespace Synthesis.Domains.Electronics.Phasor
set_option autoImplicit false

/-! # The series resonant branch

A series resistor-inductor-capacitor branch at a fixed angular frequency. The reactance
cancels exactly at `ω₀ = 1 / sqrt (L C)`, which makes the branch purely resistive there
and, because the resistance bounds the impedance magnitude from below at every
frequency, makes `ω₀` the frequency of largest current for a fixed drive amplitude.

The description is sinusoidal steady state: it presupposes a single angular frequency,
linearity and decayed transients. Start-up, large-signal behaviour and distortion are
outside it. -/

open Complex

/-- A series resistor-inductor-capacitor branch with nondegenerate parameters. -/
structure SeriesRLC where
  resistance : ℝ
  inductance : ℝ
  capacitance : ℝ
  resistancePositive : 0 < resistance
  inductancePositive : 0 < inductance
  capacitancePositive : 0 < capacitance

namespace SeriesRLC

/-- Driving-point impedance of the series branch at angular frequency `ω`. -/
noncomputable def impedance (s : SeriesRLC) (frequency : ℝ) : ℂ :=
  (s.resistance : ℂ) +
    Complex.I * ((frequency * s.inductance - 1 / (frequency * s.capacitance) : ℝ) : ℂ)

theorem impedance_re (s : SeriesRLC) (frequency : ℝ) :
    (s.impedance frequency).re = s.resistance := by
  simp [impedance]

theorem impedance_im (s : SeriesRLC) (frequency : ℝ) :
    (s.impedance frequency).im = frequency * s.inductance - 1 / (frequency * s.capacitance) := by
  simp [impedance]

/-- The branch impedance is the series combination of the three element impedances. -/
theorem impedance_series (s : SeriesRLC) (frequency : ℝ) :
    s.impedance frequency =
      seriesImpedance (seriesImpedance (resistor s.resistance) (inductor s.inductance frequency))
        (capacitor s.capacitance frequency) := by
  simp only [impedance, seriesImpedance, resistor, inductor, capacitor]
  push_cast
  ring

/-- A passive series branch never has negative resistance. -/
theorem impedance_passive (s : SeriesRLC) (frequency : ℝ) : 0 ≤ (s.impedance frequency).re := by
  rw [impedance_re]
  exact le_of_lt s.resistancePositive

/-- Angular resonance frequency `1 / sqrt (L C)`. -/
noncomputable def resonance (s : SeriesRLC) : ℝ := 1 / Real.sqrt (s.inductance * s.capacitance)

theorem resonance_positive (s : SeriesRLC) : 0 < s.resonance := by
  have product : 0 < s.inductance * s.capacitance :=
    mul_pos s.inductancePositive s.capacitancePositive
  exact one_div_pos.mpr (Real.sqrt_pos.mpr product)

/-- The defining relation of the resonance frequency: `ω₀² L C = 1`. -/
theorem resonance_squared (s : SeriesRLC) : s.resonance ^ 2 * (s.inductance * s.capacitance) = 1 := by
  have product : 0 < s.inductance * s.capacitance :=
    mul_pos s.inductancePositive s.capacitancePositive
  have root : Real.sqrt (s.inductance * s.capacitance) ^ 2 = s.inductance * s.capacitance :=
    Real.sq_sqrt (le_of_lt product)
  have nonzero : Real.sqrt (s.inductance * s.capacitance) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr product)
  simp only [resonance, div_pow, one_pow]
  rw [root]
  field_simp
  exact div_self (ne_of_gt product)

/-- **Resonance**: the reactance cancels exactly at `ω₀`, so the branch is purely
resistive there. -/
theorem impedance_at_resonance (s : SeriesRLC) : s.impedance s.resonance = (s.resistance : ℂ) := by
  have frequency : s.resonance ≠ 0 := ne_of_gt s.resonance_positive
  have capacitance : s.capacitance ≠ 0 := ne_of_gt s.capacitancePositive
  have cancel :
      s.resonance * s.inductance - 1 / (s.resonance * s.capacitance) = 0 := by
    have squared := s.resonance_squared
    field_simp
    linear_combination squared
  simp only [impedance, cancel]
  push_cast
  ring

theorem reactance_zero_at_resonance (s : SeriesRLC) : (s.impedance s.resonance).im = 0 := by
  rw [impedance_at_resonance]
  simp

/-- The impedance magnitude is bounded below by the resistance at every frequency. -/
theorem resistance_le_norm (s : SeriesRLC) (frequency : ℝ) :
    s.resistance ≤ ‖s.impedance frequency‖ := by
  have bound := Complex.re_le_norm (s.impedance frequency)
  rwa [impedance_re] at bound

/-- **The resonance frequency minimizes the impedance magnitude**, so a series resonant
branch draws its largest current there for a fixed drive amplitude. -/
theorem resonance_minimizes_norm (s : SeriesRLC) (frequency : ℝ) :
    ‖s.impedance s.resonance‖ ≤ ‖s.impedance frequency‖ := by
  have value : ‖s.impedance s.resonance‖ = s.resistance := by
    rw [impedance_at_resonance, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos s.resistancePositive]
  rw [value]
  exact resistance_le_norm s frequency

/-- Quality factor of the branch. -/
noncomputable def quality (s : SeriesRLC) : ℝ :=
  Real.sqrt (s.inductance / s.capacitance) / s.resistance

theorem quality_positive (s : SeriesRLC) : 0 < s.quality := by
  have ratio : 0 < s.inductance / s.capacitance :=
    div_pos s.inductancePositive s.capacitancePositive
  exact div_pos (Real.sqrt_pos.mpr ratio) s.resistancePositive

/-- A higher resistance gives a lower quality factor at fixed reactive parameters. -/
theorem quality_antitone (s t : SeriesRLC) (sameL : s.inductance = t.inductance)
    (sameC : s.capacitance = t.capacitance) (damped : s.resistance ≤ t.resistance) :
    t.quality ≤ s.quality := by
  have ratio : 0 < s.inductance / s.capacitance :=
    div_pos s.inductancePositive s.capacitancePositive
  simp only [quality, sameL, sameC]
  apply div_le_div_of_nonneg_left _ s.resistancePositive damped
  rw [sameL, sameC] at ratio
  exact le_of_lt (Real.sqrt_pos.mpr ratio)

end SeriesRLC
end Synthesis.Domains.Electronics.Phasor
