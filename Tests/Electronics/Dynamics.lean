import Synthesis
import Synthesis.Domains
import Synthesis.Bridges

namespace Tests.Electronics
open Synthesis Synthesis.Physics Synthesis.Domains Synthesis.Semantics
set_option autoImplicit false

/-! Regression checks for the time-domain and frequency-domain layers: energy storage,
the first-order and second-order relaxations, the derived series circuit equation, the
resonant branch, sinusoidal power and the first-order filter responses. -/

/-! ## Storage, transients and sinusoidal steady state -/

noncomputable def realCapacitor : Electronics.Storage.Capacitor := ⟨2, by norm_num⟩

example : realCapacitor.energy 3 = 9 := by
  norm_num [Electronics.Storage.Capacitor.energy, realCapacitor]

example : 0 ≤ realCapacitor.energy (-4) :=
  Electronics.Storage.Capacitor.energy_nonneg realCapacitor (-4)

noncomputable def relaxation : Electronics.Transient.FirstOrder := ⟨1 / 2, by norm_num⟩

example : relaxation.natural 7 0 = 7 := relaxation.natural_zero 7

example : relaxation.step 1 5 0 = 1 := relaxation.step_zero 1 5

-- The closed form is the only solution of the first-order equation.
example (x rate : ℝ → ℝ) (differentiable : ∀ t, HasDerivAt x (rate t) t)
    (ode : ∀ t, relaxation.timeConstant * rate t + x t = 0) (t : ℝ) :
    x t = relaxation.natural (x 0) t :=
  Electronics.Transient.FirstOrder.natural_unique relaxation x rate differentiable ode t

noncomputable def tank : Electronics.Phasor.SeriesRLC := ⟨10, 1, 1 / 4, by norm_num, by norm_num, by norm_num⟩

example : tank.impedance tank.resonance = (10 : ℂ) := by
  have value := tank.impedance_at_resonance
  norm_num [tank] at value ⊢
  exact value

example (frequency : ℝ) : ‖tank.impedance tank.resonance‖ ≤ ‖tank.impedance frequency‖ :=
  tank.resonance_minimizes_norm frequency

-- An ideal reactance dissipates no average power.
example (amplitude : ℝ) :
    Electronics.Phasor.averagePower (Electronics.Phasor.inductor 1 (2 : ℝ)) amplitude = 0 :=
  Electronics.Phasor.inductor_average_power 1 2 amplitude

/-! ## Second-order relaxation and the RLC circuits -/

open Electronics.SecondOrder

/-- Dissipation `3`, stiffness `2`: discriminant `1`, so the relaxation is overdamped
with the characteristic roots `-1` and `-2`. -/
def overdampedRelaxation : Damped := ⟨3, 2, by norm_num, by norm_num⟩

example : overdampedRelaxation.discriminant = 1 := by
  norm_num [Damped.discriminant, overdampedRelaxation]

example : overdampedRelaxation.characteristic (-1) = 0 := by
  norm_num [Damped.characteristic, overdampedRelaxation]

example : overdampedRelaxation.slowRoot = -1 := by
  have value : overdampedRelaxation.discriminant = 1 := by
    norm_num [Damped.discriminant, overdampedRelaxation]
  simp only [Damped.slowRoot, value, Real.sqrt_one]
  norm_num [overdampedRelaxation]

example : overdampedRelaxation.slowRoot < 0 :=
  Damped.slowRoot_negative (by norm_num [Damped.discriminant, overdampedRelaxation])

-- Every characteristic root gives a solution of the relaxation.
example : overdampedRelaxation.Solves (mode (-1) 5) (mode (-1) (-1 * 5))
    (mode (-1) (-1 * (-1 * 5))) :=
  mode_solves overdampedRelaxation
    (by norm_num [Damped.characteristic, overdampedRelaxation]) 5

-- Every solution of an overdamped relaxation is a combination of its two modes.
example (x rate acceleration : ℝ → ℝ)
    (solution : overdampedRelaxation.Solves x rate acceleration) :
    ∃ a b : ℝ, x = fun t => a * Real.exp (overdampedRelaxation.fastRoot * t) +
      b * Real.exp (overdampedRelaxation.slowRoot * t) :=
  overdamped_decomposition overdampedRelaxation
    (by norm_num [Damped.discriminant, overdampedRelaxation]) solution

/-- Dissipation `1`, stiffness `4`: discriminant `-15`, so the response oscillates. -/
def underdampedRelaxation : Damped := ⟨1, 4, by norm_num, by norm_num⟩

-- Below critical damping no real exponential mode exists at all.
example (s : ℝ) : 0 < underdampedRelaxation.characteristic s :=
  no_real_root underdampedRelaxation
    (by norm_num [Damped.discriminant, underdampedRelaxation]) s

-- The decaying sinusoid family solves the underdamped relaxation.
example (a b : ℝ) : underdampedRelaxation.Solves
    (oscillatoryMode underdampedRelaxation.decayRate underdampedRelaxation.dampedFrequency a b)
    (oscillatoryMode underdampedRelaxation.decayRate underdampedRelaxation.dampedFrequency
      (-underdampedRelaxation.decayRate * a + underdampedRelaxation.dampedFrequency * b)
      (-underdampedRelaxation.decayRate * b - underdampedRelaxation.dampedFrequency * a))
    (oscillatoryMode underdampedRelaxation.decayRate underdampedRelaxation.dampedFrequency
      (-underdampedRelaxation.decayRate *
          (-underdampedRelaxation.decayRate * a + underdampedRelaxation.dampedFrequency * b) +
        underdampedRelaxation.dampedFrequency *
          (-underdampedRelaxation.decayRate * b - underdampedRelaxation.dampedFrequency * a))
      (-underdampedRelaxation.decayRate *
          (-underdampedRelaxation.decayRate * b - underdampedRelaxation.dampedFrequency * a) -
        underdampedRelaxation.dampedFrequency *
          (-underdampedRelaxation.decayRate * a +
            underdampedRelaxation.dampedFrequency * b))) :=
  oscillatory_solves underdampedRelaxation
    (by norm_num [Damped.discriminant, underdampedRelaxation]) a b

-- The ringing stays inside its exponential envelope.
example (a b t : ℝ) :
    |oscillatoryMode underdampedRelaxation.decayRate underdampedRelaxation.dampedFrequency a b t| ≤
      Real.exp (-underdampedRelaxation.decayRate * t) * (|a| + |b|) :=
  oscillatory_envelope _ _ a b t

/-! ## The series RLC loop -/

noncomputable def coil : Electronics.Storage.Inductor := ⟨1, by norm_num⟩

noncomputable def reservoir : Electronics.Storage.Capacitor := ⟨1 / 2, by norm_num⟩

example : (Electronics.Rlc.seriesDamped (r := 3) (by norm_num) coil reservoir).dissipation = 3 := by
  norm_num [Electronics.Rlc.seriesDamped, coil]

-- `R² C = 4.5` exceeds `4 L = 4`, so this loop relaxes without ringing.
example : 0 < (Electronics.Rlc.seriesDamped (r := 3) (by norm_num) coil reservoir).discriminant :=
  (Electronics.Rlc.series_overdamped_iff (by norm_num) coil reservoir).mpr
    (by norm_num [coil, reservoir])

-- Halving the resistance puts the same loop below critical damping.
example : ¬(0 < (Electronics.Rlc.seriesDamped (r := 1) (by norm_num) coil reservoir).discriminant) := by
  intro overdamped
  have design := (Electronics.Rlc.series_overdamped_iff (by norm_num) coil reservoir).mp overdamped
  norm_num [coil, reservoir] at design

/-! ## Sinusoidal power and first-order filters -/

-- Instantaneous power splits into a constant and a term at twice the frequency.
example (frequency t : ℝ) :
    (2 : ℝ) * Real.cos (frequency * t + 0) * (3 * Real.cos (frequency * t)) =
      2 * 3 / 2 * (Real.cos 0 + Real.cos (2 * (frequency * t) + 0)) :=
  Electronics.Power.instantaneous_decomposition 2 3 frequency 0 t

-- The power triangle holds for every pair of terminal phasors.
example (v i : ℂ) : Electronics.Power.apparentPower v i ^ 2 =
    Electronics.Power.realPower v i ^ 2 + Electronics.Power.reactivePower v i ^ 2 :=
  Electronics.Power.apparent_sq v i

-- An ideal reactance dissipates nothing at any operating point.
example (i : ℂ) : Electronics.Power.realPower (Complex.I * i) i = 0 :=
  Electronics.Power.realPower_reactance (by simp) i

-- A passive impedance dissipates nonnegative power.
example (i : ℂ) : 0 ≤ Electronics.Power.realPower ((3 : ℂ) * i) i :=
  Electronics.Power.realPower_nonneg_of_passive (by norm_num) i

-- At the cutoff frequency the single-pole response passes exactly half the power.
example : Complex.normSq (Electronics.Filter.lowPass 1 1) = 1 / 2 :=
  Electronics.Filter.lowPass_cutoff (by norm_num)

-- The two single-pole responses are complementary in power at every frequency.
example (frequency : ℝ) :
    Complex.normSq (Electronics.Filter.lowPass 1 frequency) +
      Complex.normSq (Electronics.Filter.highPass 1 frequency) = 1 :=
  Electronics.Filter.complementary 1 frequency

example : Electronics.Filter.lowPass 5 0 = 1 := Electronics.Filter.lowPass_zero 5

-- A passive single-pole filter never amplifies.
example (frequency : ℝ) : Complex.normSq (Electronics.Filter.lowPass 2 frequency) ≤ 1 :=
  Electronics.Filter.lowPass_le_one 2 frequency

end Tests.Electronics
