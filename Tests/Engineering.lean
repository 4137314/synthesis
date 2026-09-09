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
example : (Components.resistor resistor).definition.parameters = [IR.Standard.rationalParameter "resistance" .resistance 10] := rfl

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

-- The complete parameterized IR is preserved by structural compilation.
example : (Frontend.compile (Components.resistor resistor).ir).isOk = true := by decide

-- Changed coefficients cannot reuse an interpretation for the original module.
example : (Components.resistor resistor).model.interpretation.meaning
    { (Components.resistor resistor).ir with bindings := [⟨"resistance",
      .literal IR.Standard.rational (.rational 11)⟩] } = none := by
  simp [Primitive.model, Primitive.ir, IR.Module.mk.injEq]

example : Verified (Components.resistor resistor).model ⟨fun _ => True, fun x => 0 ≤ x.power.value⟩ :=
  Components.resistor_passive resistor
example : (Bridges.Electrothermal.heat resistor current).value = 40 := by
  simp [Bridges.Electrothermal.heat, Electronics.power, Electronics.voltage, resistor, current] <;> grind

example : ¬(Quantum.Qubit.Normalized ⟨⟨2, 0⟩, ⟨0, 0⟩⟩) := by
  simp [Quantum.Qubit.Normalized, Quantum.Qubit.normSquared, Quantum.Amplitude.normSquared] <;> grind

end Tests.Engineering
