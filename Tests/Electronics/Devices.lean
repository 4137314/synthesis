import Synthesis
import Synthesis.Domains
import Synthesis.Bridges

namespace Tests.Electronics
open Synthesis Synthesis.Physics Synthesis.Domains Synthesis.Semantics
set_option autoImplicit false

/-! Regression checks for the device, feedback, logic and multiport layers, including
the negative cases that separate a passive element from an active one: an overcoupled
inductor pair and an active two-port both fail their passivity characterization. -/

/-! ## Devices, feedback and logic levels -/

noncomputable def diode : Electronics.Semiconductor.Diode := ⟨1 / 1000000000000, 1 / 40, by norm_num, by norm_num⟩

example (v : ℝ) : 0 ≤ v * diode.current v := diode.passive v

example (v : ℝ) : -(1 / 1000000000000 : ℝ) < diode.current v := diode.reverse_saturation v

example : diode.current 0 = 0 := diode.current_zero

noncomputable def transistor : Electronics.Semiconductor.Mosfet := ⟨1 / 1000, 1 / 2, by norm_num⟩

example : transistor.triodeCurrent 2 (transistor.overdrive 2) =
    transistor.saturationCurrent 2 := transistor.pinch_off_continuous 2

example : transistor.saturationCurrent transistor.threshold = 0 := transistor.cutoff

example : Electronics.Feedback.closedLoopGain (100 : ℝ) (1 / 10) ≤ 100 :=
  Electronics.Feedback.closedLoop_le_forward (by norm_num) (by norm_num)

example : Electronics.Feedback.closedLoopGain (100 : ℝ) (1 / 10) = 100 / 11 := by
  norm_num [Electronics.Feedback.closedLoopGain]

noncomputable def levels : Electronics.Digital.Discipline :=
  ⟨4 / 5, 2, 2 / 5, 12 / 5, by norm_num, by norm_num, by norm_num⟩

example : levels.marginLow = 2 / 5 := by
  norm_num [Electronics.Digital.Discipline.marginLow, levels]

example (noise : ℝ) (bounded : |noise| ≤ levels.marginLow) :
    levels.interpret (2 / 5 + noise) = some false :=
  levels.noise_immunity_low (by norm_num [levels]) bounded

-- A voltage inside the forbidden band is not interpreted as either logic value.
example : levels.interpret 1 = none :=
  levels.interpret_forbidden (by norm_num [levels]) (by norm_num [levels])

example (a b : Bool) : Electronics.Digital.nand (Electronics.Digital.nand a b)
    (Electronics.Digital.nand a b) = (a && b) := Electronics.Digital.nand_and a b

/-! ## Magnetic coupling and two-ports -/

def coupled : Electronics.Magnetics.Coupled Rat := ⟨4, 9, 6⟩

def overcoupled : Electronics.Magnetics.Coupled Rat := ⟨4, 9, 7⟩

example (i₁ i₂ : Rat) : 0 ≤ coupled.energy i₁ i₂ :=
  Electronics.Magnetics.Coupled.energy_nonneg (by norm_num [coupled]) (by norm_num [coupled]) i₁ i₂

-- Exceeding the coupling bound makes the stored energy negative at some operating point.
example : ¬∀ i₁ i₂ : Rat, 0 ≤ overcoupled.energy i₁ i₂ := by
  intro passive
  have bound := Electronics.Magnetics.Coupled.coupling_bound (c := overcoupled)
    (by norm_num [overcoupled]) passive
  norm_num [overcoupled] at bound

def transformer : Electronics.Magnetics.IdealTransformer Rat := ⟨3, by norm_num⟩

example (v i : Rat) :
    v * i + transformer.secondaryVoltage v * transformer.secondaryCurrent i = 0 :=
  transformer.power_conserved v i

def port : Electronics.TwoPort.Impedance Rat := ⟨5, 2, 2, 3⟩

example : port.Reciprocal := rfl

example (i₁ i₂ : Rat) : 0 ≤ port.absorbed i₁ i₂ :=
  Electronics.TwoPort.Impedance.passive_of_definite (by norm_num [port]) (by norm_num [port]) i₁ i₂

-- The reciprocal port is realized exactly by its T network.
example : Electronics.TwoPort.Impedance.tee (port.z11 - port.z12) port.z12
    (port.z22 - port.z12) = port :=
  Electronics.TwoPort.Impedance.tee_realizes rfl

-- Cascading preserves the reciprocity determinant.
example : (Electronics.TwoPort.Transmission.cascade
    (Electronics.TwoPort.Transmission.seriesImpedance (2 : Rat))
    (Electronics.TwoPort.Transmission.shuntAdmittance 5)).Reciprocal :=
  Electronics.TwoPort.Transmission.l_section_reciprocal 2 5

-- An active two-port violates the passivity condition.
example : ¬∀ i₁ i₂ : Rat, 0 ≤ (Electronics.TwoPort.Impedance.mk 1 4 4 1).absorbed i₁ i₂ := by
  intro passive
  have bound := Electronics.TwoPort.Impedance.definite_of_passive
    (p := Electronics.TwoPort.Impedance.mk 1 4 4 1) (by norm_num) passive
  norm_num at bound

/-! ## Admittance parameters and conversion between two-port descriptions -/

def shunted : Electronics.TwoPort.Admittance Rat := ⟨5, -2, -2, 4⟩

example : shunted.Reciprocal := rfl

example (v₁ v₂ : Rat) : 0 ≤ shunted.absorbed v₁ v₂ :=
  Electronics.TwoPort.Admittance.passive_of_definite (by norm_num [shunted])
    (by norm_num [shunted]) v₁ v₂

-- The reciprocal admittance port is realized exactly by its Pi network.
example : Electronics.TwoPort.Admittance.pi (shunted.y11 + shunted.y12) (-shunted.y12)
    (shunted.y22 + shunted.y12) = shunted :=
  Electronics.TwoPort.Admittance.pi_realizes rfl

example : port.determinant = 11 := by
  norm_num [Electronics.TwoPort.Impedance.determinant, port]

-- Converting to admittance parameters and back is the identity on a nondegenerate port.
example : port.toAdmittance.toImpedance = port :=
  Electronics.TwoPort.toImpedance_toAdmittance
    (by norm_num [Electronics.TwoPort.Impedance.determinant, port])

-- The converted parameters reproduce the port current, which is what correctness means.
example (i₁ i₂ : Rat) :
    port.toAdmittance.primaryCurrent (port.primaryVoltage i₁ i₂) (port.secondaryVoltage i₁ i₂) = i₁ :=
  Electronics.TwoPort.toAdmittance_primary
    (by norm_num [Electronics.TwoPort.Impedance.determinant, port]) i₁ i₂

-- Impedance reciprocity and the transmission determinant identity are the same condition.
example : port.toTransmission.Reciprocal :=
  Electronics.TwoPort.toTransmission_reciprocal (by norm_num [port]) rfl

-- A nonreciprocal port fails the transmission identity as well.
example : ¬(Electronics.TwoPort.Impedance.mk (5 : Rat) 2 4 3).toTransmission.Reciprocal := by
  intro reciprocal
  have transfer := (Electronics.TwoPort.toTransmission_reciprocal_iff
    (p := Electronics.TwoPort.Impedance.mk (5 : Rat) 2 4 3) (by norm_num)).mp reciprocal
  norm_num [Electronics.TwoPort.Impedance.Reciprocal] at transfer

end Tests.Electronics
