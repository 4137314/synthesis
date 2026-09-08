import Synthesis
import Synthesis.Domains.Components
import Synthesis.Bridges

namespace Tests.Engineering
open Synthesis Synthesis.Physics Synthesis.Domains Synthesis.Semantics
set_option autoImplicit false

/-- Concrete nonzero operating points exercise the rational model, not only zero witnesses. -/
def resistor : Electronics.Resistor := ⟨⟨10⟩, by decide⟩
def current : Electronics.Current := ⟨-2⟩

example : (Electronics.voltage resistor current).value = -20 := by
  simp [Electronics.voltage, resistor, current] <;> grind
example : (Electronics.power resistor current).value = 40 := by
  simp [Electronics.power, Electronics.voltage, resistor, current] <;> grind
example : (Components.resistor resistor).component.parameters = [⟨"resistance", .resistance, 10⟩] := rfl

example : True := by
  fail_if_success
    have _ : Electronics.Resistor := ⟨⟨-1⟩, by decide⟩
  trivial

example : True := by
  fail_if_success
    have _ := Electronics.voltage resistor (⟨2⟩ : Quantity Rat Dimension.timeDim)
  trivial

example : True := by
  fail_if_success
    have _ : Mechanics.ElasticMaterial := ⟨⟨0⟩, by decide⟩
  trivial

def link : Thermal.Link := ⟨⟨2⟩, by decide⟩
example : (Thermal.heatRate link ⟨300⟩ ⟨310⟩).value = -20 := by
  simp [Thermal.heatRate, link] <;> grind

example : ¬(0 ≤ (Thermal.heatRate link ⟨300⟩ ⟨310⟩).value) := by
  simp [Thermal.heatRate, link] <;> grind

def material : Mechanics.ElasticMaterial := ⟨⟨200⟩, by decide⟩
example : (Mechanics.energyDensity material ⟨1 / 10⟩).value = 1 := by
  simp [Mechanics.energyDensity, material] <;> grind

def splitter : Photonics.Splitter := ⟨1 / 2, 1 / 4, by grind, by grind, by grind⟩
def opticalInput : Photonics.OpticalPower := ⟨⟨8⟩, by decide⟩
example : (Photonics.absorbed splitter opticalInput).value = 2 := by
  simp [Photonics.absorbed, splitter, opticalInput] <;> grind
example : ¬((3 / 4 : Rat) + 1 / 2 ≤ 1) := by grind

-- Demonstrate that a missing reactant violates oxygen conservation.
def unbalanced : Chemistry.Reaction Chemistry.Water.Molecule :=
  ⟨[.hydrogen, .oxygen], [.water]⟩
example : ¬unbalanced.BalancedElements Chemistry.Water.atoms := by
  intro h
  have oxygen := h Chemistry.Water.Element.oxygen
  simp [Chemistry.Reaction.Balanced, Chemistry.inventory, unbalanced, Chemistry.Water.atoms] at oxygen

-- The network theorem covers a genuine reaction step in a surrounding batch.
example : Systems.Reachable
    (Chemistry.network [Chemistry.Water.formation]
      [.hydrogen, .hydrogen, .oxygen, .water]) [.water, .water, .water] := by
  apply Systems.Reachable.step (s := [.hydrogen, .hydrogen, .oxygen, .water])
  · exact .initial rfl
  · exact ⟨Chemistry.Water.formation, by simp, [.water], rfl, rfl⟩

-- A normalized superposition with exact rational amplitudes.
def qubit : Quantum.Qubit := ⟨⟨3 / 5, 0⟩, ⟨0, 4 / 5⟩⟩
example : qubit.Normalized := by
  simp [Quantum.Qubit.Normalized, Quantum.Qubit.normSquared, Quantum.Amplitude.normSquared, qubit] <;> grind

example : (Quantum.x.andThen Quantum.phase).run qubit = Quantum.phase.run (Quantum.x.run qubit) := rfl

-- The generic component recognizer cannot accept altered coefficients or interfaces.
example : (Components.resistor resistor).model.interpretation.component
    { (Components.resistor resistor).component with parameters := [⟨"resistance", .resistance, 11⟩] } = none := by
  simp [Primitive.model, Components.resistor, resistor, IR.Component.mk.injEq, Parameter.mk.injEq] <;> decide
example : (Components.resistor resistor).model.interpretation.component
    { (Components.resistor resistor).component with ports := [] } = none := by
  simp [Primitive.model, Components.resistor, IR.Component.mk.injEq]

-- AST schema 2 rejects duplicate parameter names and preserves coefficients on compilation.
def duplicateParameter : Frontend.Design := {
  name := "bad-parameters"
  components := [{ (Components.resistor resistor).component with parameters :=
    [⟨"resistance", .resistance, 10⟩, ⟨"resistance", .resistance, 20⟩] }]
}
example : (Frontend.compile duplicateParameter).isOk = false := by decide

/-- The typed frontend carries the exact parameterized model into the consumer boundary. -/
def compiledResistor : Except Frontend.CompileError (Model Components.ElectricalPoint) :=
  Frontend.compileModel
    ⟨(Components.resistor resistor).component.name, [(Components.resistor resistor).component], []⟩
    (Components.resistor resistor).model.interpretation
    (Components.resistor resistor).model.supported

example : compiledResistor.isOk = true := by decide
example : Verified (Components.resistor resistor).model ⟨fun _ => True, fun x => 0 ≤ x.power.value⟩ :=
  Components.resistor_passive resistor
example : (Bridges.Electrothermal.heat resistor current).value = 40 := by
  simp [Bridges.Electrothermal.heat, Electronics.power, Electronics.voltage, resistor, current] <;> grind

example : ¬(Quantum.Qubit.Normalized ⟨⟨2, 0⟩, ⟨0, 0⟩⟩) := by
  simp [Quantum.Qubit.Normalized, Quantum.Qubit.normSquared, Quantum.Amplitude.normSquared] <;> grind

example : (Components.resistor resistor).model.interpretation.component
    { (Components.resistor resistor).component with parameters := [⟨"resistance", .timeDim, 10⟩] } = none := by
  simp [Primitive.model, Components.resistor, resistor, IR.Component.mk.injEq,
    Parameter.mk.injEq, Dimension.resistance, Dimension.timeDim] <;> decide

example : (Frontend.compile {
    name := "empty-parameter"
    components := [{ (Components.resistor resistor).component with
      parameters := [⟨"", .resistance, 10⟩] }] }).isOk = false := by decide

end Tests.Engineering
