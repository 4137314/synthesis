import Synthesis.Domains.Electronics
import Synthesis.Semantics.Primitive
import Synthesis.IR.Standard

namespace Synthesis.Domains.Components
open Physics Semantics
set_option autoImplicit false

structure ElectricalPoint where
  current : Electronics.Current
  voltage : Electronics.Voltage
  power : Electronics.Power

def resistor (r : Electronics.Resistor) : Primitive ElectricalPoint where
  definition := {
    id := ⟨["synthesis.models", "resistor"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.electronics.resistor.v1")]
    ports := [IR.Standard.observable "synthesis.electronics" "current" .currentDim,
      IR.Standard.observable "synthesis.electronics" "voltage" .voltage,
      IR.Standard.observable "synthesis.electronics" "power" .power]
    parameters := [IR.Standard.rationalParameter "resistance" .resistance (r.quantity.value)]
  }
  meaning x := x.voltage = Electronics.voltage r x.current ∧ x.power = Electronics.power r x.current
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem resistor_passive (r : Electronics.Resistor) :
    Verified (resistor r).model ⟨fun _ => True, fun x => 0 ≤ x.power.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, Electronics.voltage r ⟨0⟩, Electronics.power r ⟨0⟩⟩, ⟨rfl, rfl⟩, trivial⟩
  · intro x hx _
    change 0 ≤ x.power.value
    rw [hx.2]
    exact Electronics.passive r x.current

structure ConductorPoint where
  voltage : Electronics.Voltage
  current : Electronics.Current
  power : Electronics.Power

/-- Conductance form of the ideal resistive element; the dual of `resistor`. -/
def conductor (g : Electronics.Conductor) : Primitive ConductorPoint where
  definition := {
    id := ⟨["synthesis.models", "conductor"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.electronics.conductor.v1")]
    ports := [IR.Standard.observable "synthesis.electronics" "voltage" .voltage,
      IR.Standard.observable "synthesis.electronics" "current" .currentDim,
      IR.Standard.observable "synthesis.electronics" "power" .power]
    parameters := [IR.Standard.rationalParameter "conductance" .conductance (g.quantity.value)]
  }
  meaning x := x.current = Electronics.current g x.voltage ∧
    x.power = Electronics.conductorPower g x.voltage
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem conductor_passive (g : Electronics.Conductor) :
    Verified (conductor g).model ⟨fun _ => True, fun x => 0 ≤ x.power.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, Electronics.current g ⟨0⟩, Electronics.conductorPower g ⟨0⟩⟩, ⟨rfl, rfl⟩, trivial⟩
  · intro x hx _
    change 0 ≤ x.power.value
    rw [hx.2]
    exact Electronics.conductor_passive g x.voltage

structure CapacitorPoint where
  voltage : Electronics.Voltage
  charge : Electronics.Charge
  energy : Electronics.Energy

/-- Ideal linear capacitor at a fixed operating point: stored charge and energy as
functions of the terminal voltage. The time-domain law is not part of this interface. -/
def capacitor (c : Electronics.Capacitor) : Primitive CapacitorPoint where
  definition := {
    id := ⟨["synthesis.models", "capacitor"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.electronics.capacitor.v1")]
    ports := [IR.Standard.observable "synthesis.electronics" "voltage" .voltage,
      IR.Standard.observable "synthesis.electronics" "charge" .charge,
      IR.Standard.observable "synthesis.electronics" "energy" .energy]
    parameters := [IR.Standard.rationalParameter "capacitance" .capacitance (c.quantity.value)]
  }
  meaning x := x.charge = Electronics.charge c x.voltage ∧
    x.energy = Electronics.capacitiveEnergy c x.voltage
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem capacitor_energy_nonnegative (c : Electronics.Capacitor) :
    Verified (capacitor c).model ⟨fun _ => True, fun x => 0 ≤ x.energy.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, Electronics.charge c ⟨0⟩, Electronics.capacitiveEnergy c ⟨0⟩⟩, ⟨rfl, rfl⟩, trivial⟩
  · intro x hx _
    change 0 ≤ x.energy.value
    rw [hx.2]
    exact Electronics.capacitive_energy_nonnegative c x.voltage

structure InductorPoint where
  current : Electronics.Current
  flux : Electronics.Flux
  energy : Electronics.Energy

/-- Ideal linear inductor at a fixed operating point: flux linkage and stored energy as
functions of the branch current. -/
def inductor (l : Electronics.Inductor) : Primitive InductorPoint where
  definition := {
    id := ⟨["synthesis.models", "inductor"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.electronics.inductor.v1")]
    ports := [IR.Standard.observable "synthesis.electronics" "current" .currentDim,
      IR.Standard.observable "synthesis.electronics" "flux" .magneticFlux,
      IR.Standard.observable "synthesis.electronics" "energy" .energy]
    parameters := [IR.Standard.rationalParameter "inductance" .inductance (l.quantity.value)]
  }
  meaning x := x.flux = Electronics.flux l x.current ∧
    x.energy = Electronics.inductiveEnergy l x.current
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem inductor_energy_nonnegative (l : Electronics.Inductor) :
    Verified (inductor l).model ⟨fun _ => True, fun x => 0 ≤ x.energy.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, Electronics.flux l ⟨0⟩, Electronics.inductiveEnergy l ⟨0⟩⟩, ⟨rfl, rfl⟩, trivial⟩
  · intro x hx _
    change 0 ≤ x.energy.value
    rw [hx.2]
    exact Electronics.inductive_energy_nonnegative l x.current

structure SourcePoint where
  current : Electronics.Current
  delivered : Electronics.Power

/-- Ideal independent voltage source. It is an active element: its certificate below is
conditional on a stated current direction, and no passivity theorem is available. -/
def voltageSource (s : Electronics.VoltageSource) : Primitive SourcePoint where
  definition := {
    id := ⟨["synthesis.models", "voltage-source"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.electronics.voltage-source.v1")]
    ports := [IR.Standard.observable "synthesis.electronics" "current" .currentDim,
      IR.Standard.observable "synthesis.electronics" "delivered" .power]
    parameters := [IR.Standard.rationalParameter "electromotive-force" .voltage (s.emf.value)]
  }
  meaning x := x.delivered = s.delivered x.current
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

/-- Inside the stated operating envelope, a source with nonnegative electromotive force
delivers nonnegative power. Outside it the source absorbs, which is why the assumption
is part of the contract rather than a global claim. -/
theorem source_delivers (s : Electronics.VoltageSource) (oriented : 0 ≤ s.emf.value) :
    Verified (voltageSource s).model
      ⟨fun x => 0 ≤ x.current.value, fun x => 0 ≤ x.delivered.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, s.delivered ⟨0⟩⟩, rfl, Rat.le_refl⟩
  · intro x hx ha
    change 0 ≤ x.delivered.value
    rw [hx]
    exact Rat.mul_nonneg oriented ha

end Synthesis.Domains.Components
