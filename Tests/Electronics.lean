import Synthesis
import Synthesis.Domains
import Synthesis.Bridges

namespace Tests.Electronics
open Synthesis Synthesis.Physics Synthesis.Domains Synthesis.Semantics
set_option autoImplicit false

/-! Regression checks for the electronics domain. Positive cases evaluate the models at
concrete operating points; negative cases exercise rejection paths: excluded parameters,
mismatched dimensions, altered component interfaces and violated assumptions. -/

/-! ## Exact rational element models -/

def capacitor : Electronics.Capacitor := ⟨⟨1 / 1000⟩, by norm_num⟩
def inductor : Electronics.Inductor := ⟨⟨2⟩, by norm_num⟩
def conductor : Electronics.Conductor := ⟨⟨1 / 4⟩, by norm_num⟩
def source : Electronics.VoltageSource := ⟨⟨12⟩⟩

example : (Electronics.charge capacitor ⟨10⟩).value = 1 / 100 := by
  norm_num [Electronics.charge, capacitor]

example : (Electronics.capacitiveEnergy capacitor ⟨10⟩).value = 1 / 20 := by
  norm_num [Electronics.capacitiveEnergy, capacitor]

example : (Electronics.inductiveEnergy inductor ⟨3⟩).value = 9 := by
  norm_num [Electronics.inductiveEnergy, inductor]

example : (Electronics.flux inductor ⟨3⟩).value = 6 := by
  norm_num [Electronics.flux, inductor]

example : (Electronics.current conductor ⟨8⟩).value = 2 := by
  norm_num [Electronics.current, conductor]

example : (source.delivered ⟨-1⟩).value = -12 := by
  norm_num [Electronics.VoltageSource.delivered, source]

-- Degenerate storage parameters are excluded by the element types.
example : True := by
  fail_if_success
    have _ : Electronics.Capacitor := ⟨⟨0⟩, by decide⟩
  trivial

example : True := by
  fail_if_success
    have _ : Electronics.Inductor := ⟨⟨-1⟩, by decide⟩
  trivial

example : True := by
  fail_if_success
    have _ : Electronics.Conductor := ⟨⟨-1⟩, by decide⟩
  trivial

-- A capacitance cannot be applied to a current: dimensions are checked by elaboration.
example : True := by
  fail_if_success
    have _ := Electronics.charge capacitor (⟨2⟩ : Quantity Rat Dimension.currentDim)
  trivial

-- Reciprocal parameters exist only for nondegenerate elements.
example : (Electronics.elastance capacitor).quantity.value = 1000 := by
  norm_num [Electronics.elastance, capacitor]

/-! ## Certificates on the compiled component catalog -/

example : (Components.capacitor capacitor).component.parameters =
    [⟨"capacitance", .capacitance, 1 / 1000⟩] := rfl

example : (Components.inductor inductor).component.operation =
    "synthesis.electronics.inductor.v1" := rfl

example : Verified (Components.capacitor capacitor).model
    ⟨fun _ => True, fun x => 0 ≤ x.energy.value⟩ :=
  Components.capacitor_energy_nonnegative capacitor

example : Verified (Components.inductor inductor).model
    ⟨fun _ => True, fun x => 0 ≤ x.energy.value⟩ :=
  Components.inductor_energy_nonnegative inductor

example : Verified (Components.conductor conductor).model
    ⟨fun _ => True, fun x => 0 ≤ x.power.value⟩ :=
  Components.conductor_passive conductor

example : Verified (Components.voltageSource source).model
    ⟨fun x => 0 ≤ x.current.value, fun x => 0 ≤ x.delivered.value⟩ :=
  Components.source_delivers source (by decide)

-- A changed coefficient is not the same component and has no interpretation.
example : (Components.capacitor capacitor).model.interpretation.component
    { (Components.capacitor capacitor).component with
      parameters := [⟨"capacitance", .capacitance, 1 / 500⟩] } = none := by
  simp [Primitive.model, Components.capacitor, capacitor, IR.Component.mk.injEq,
    Parameter.mk.injEq]

-- A changed parameter dimension is likewise unsupported.
example : (Components.inductor inductor).model.interpretation.component
    { (Components.inductor inductor).component with
      parameters := [⟨"inductance", .capacitance, 2⟩] } = none := by
  simp [Primitive.model, Components.inductor, inductor, IR.Component.mk.injEq,
    Parameter.mk.injEq, Dimension.inductance, Dimension.capacitance]

-- The compiled graph of a storage element remains structurally valid.
example : (Frontend.compile {
    name := "capacitor-bank"
    components := [(Components.capacitor capacitor).component] }).isOk = true := by decide

-- Duplicate parameters are rejected at the frontend.
example : (Frontend.compile {
    name := "bad-capacitor"
    components := [{ (Components.capacitor capacitor).component with
      parameters := [⟨"capacitance", .capacitance, 1⟩, ⟨"capacitance", .capacitance, 2⟩] }]
    }).isOk = false := by decide

/-! ## Two-terminal element algebra over the exact rationals -/

open Electronics.Element.TwoTerminal

example : Passive (resistor (10 : Rat)) := (resistor_passive_iff 10).mpr (by norm_num)

example : ¬Passive (resistor (-1 : Rat)) := by
  intro h
  have := (resistor_passive_iff (-1 : Rat)).mp h
  norm_num at this

example : ¬Passive (voltageSource (5 : Rat)) := voltage_source_not_passive (by norm_num)

example : Equivalent (series (resistor (3 : Rat)) (resistor 4)) (resistor 7) := by
  have combined := series_resistor (3 : Rat) 4
  norm_num at combined
  exact combined

example : Equivalent (thevenin (10 : Rat) 5) (norton 2 (1 / 5 : Rat)) := by
  have equivalence := thevenin_norton (e := (10 : Rat)) (r := 5) (by norm_num)
  norm_num at equivalence
  exact equivalence

/-! ## Interconnection laws -/

/-- Two branches between two nodes, oriented in opposite directions. -/
def loop : Electronics.Network.Topology (Fin 2) (Fin 2) :=
  ⟨fun b => if b = 0 then 0 else 1, fun b => if b = 0 then 1 else 0⟩

def potential : Fin 2 → Rat := fun n => if n = 0 then 5 else 0

def loopCurrent : Fin 2 → Rat := fun _ => 2

example : Electronics.Network.KCL loop loopCurrent := by
  intro n
  fin_cases n <;>
    norm_num [Electronics.Network.injection, Electronics.Network.incidence, loop, loopCurrent,
      Fin.sum_univ_two]

-- Tellegen's theorem on a concrete interconnection: the branch powers cancel exactly.
example : ∑ b, Electronics.Network.branchVoltage loop potential b * loopCurrent b = 0 := by
  refine Electronics.Network.tellegen loop potential loopCurrent ?_
  intro n
  fin_cases n <;>
    norm_num [Electronics.Network.injection, Electronics.Network.incidence, loop, loopCurrent,
      Fin.sum_univ_two]

-- A current assignment that violates Kirchhoff's law is rejected.
example : ¬Electronics.Network.KCL loop (fun b => if b = 0 then (2 : Rat) else 3) := by
  intro kcl
  have node := kcl 0
  norm_num [Electronics.Network.injection, Electronics.Network.incidence, loop,
    Fin.sum_univ_two] at node

/-! ## Resistive interconnection, sources and transfer -/

example : Electronics.Resistive.parallel (6 : Rat) 3 = 2 := by
  norm_num [Electronics.Resistive.parallel]

example : Electronics.Resistive.dividerVoltage (1 : Rat) 3 8 = 6 := by
  norm_num [Electronics.Resistive.dividerVoltage]

example : Electronics.Resistive.bridge (2 : Rat) 4 3 6 12 = 0 :=
  (Electronics.Resistive.bridge_balanced_iff (r1 := (2 : Rat)) (r2 := 4) (r3 := 3) (r4 := 6) (vin := 12)
    (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)

example : Electronics.Resistive.bridge (2 : Rat) 4 3 5 12 ≠ 0 := by
  intro balanced
  have condition := (Electronics.Resistive.bridge_balanced_iff (r1 := (2 : Rat)) (r2 := 4) (r3 := 3) (r4 := 5)
    (vin := 12) (by norm_num) (by norm_num) (by norm_num)).mp balanced
  norm_num at condition

example : Electronics.Source.loadPower (10 : ℝ) 5 5 = 5 := by
  rw [Electronics.Source.matched_load_power (by norm_num)]
  norm_num

example (load : ℝ) (external : 0 ≤ load) :
    Electronics.Source.loadPower (10 : ℝ) 5 load ≤ 5 := by
  have bound := Electronics.Source.maximum_power_transfer (e := (10 : ℝ)) (r := 5) (by norm_num) external
  norm_num at bound
  exact bound

example : Electronics.Source.efficiency (5 : ℝ) 5 = 1 / 2 :=
  Electronics.Source.matched_efficiency (by norm_num)

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

end Tests.Electronics
