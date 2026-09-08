import Synthesis.Domains.Chemistry
import Synthesis.Domains.Electronics
import Synthesis.Domains.Thermal
import Synthesis.Domains.Mechanics
import Synthesis.Domains.Photonics
import Synthesis.Domains.Quantum
import Synthesis.Semantics.Primitive

namespace Synthesis.Domains.Components
open Physics Semantics
set_option autoImplicit false

structure ElectricalPoint where
  current : Electronics.Current
  voltage : Electronics.Voltage
  power : Electronics.Power

def resistor (r : Electronics.Resistor) : Primitive ElectricalPoint where
  component := {
    name := "resistor"
    operation := "synthesis.electronics.resistor.v1"
    ports := [⟨"current", .input, .quantity .electronics .currentDim⟩,
      ⟨"voltage", .output, .quantity .electronics .voltage⟩,
      ⟨"power", .output, .quantity .electronics .power⟩]
    parameters := [⟨"resistance", .resistance, r.quantity.value⟩]
  }
  meaning x := x.voltage = Electronics.voltage r x.current ∧ x.power = Electronics.power r x.current
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

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
  component := {
    name := "conductor"
    operation := "synthesis.electronics.conductor.v1"
    ports := [⟨"voltage", .input, .quantity .electronics .voltage⟩,
      ⟨"current", .output, .quantity .electronics .currentDim⟩,
      ⟨"power", .output, .quantity .electronics .power⟩]
    parameters := [⟨"conductance", .conductance, g.quantity.value⟩]
  }
  meaning x := x.current = Electronics.current g x.voltage ∧
    x.power = Electronics.conductorPower g x.voltage
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

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
  component := {
    name := "capacitor"
    operation := "synthesis.electronics.capacitor.v1"
    ports := [⟨"voltage", .input, .quantity .electronics .voltage⟩,
      ⟨"charge", .output, .quantity .electronics .charge⟩,
      ⟨"energy", .output, .quantity .electronics .energy⟩]
    parameters := [⟨"capacitance", .capacitance, c.quantity.value⟩]
  }
  meaning x := x.charge = Electronics.charge c x.voltage ∧
    x.energy = Electronics.capacitiveEnergy c x.voltage
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

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
  component := {
    name := "inductor"
    operation := "synthesis.electronics.inductor.v1"
    ports := [⟨"current", .input, .quantity .electronics .currentDim⟩,
      ⟨"flux", .output, .quantity .electronics .magneticFlux⟩,
      ⟨"energy", .output, .quantity .electronics .energy⟩]
    parameters := [⟨"inductance", .inductance, l.quantity.value⟩]
  }
  meaning x := x.flux = Electronics.flux l x.current ∧
    x.energy = Electronics.inductiveEnergy l x.current
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

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
  component := {
    name := "voltage-source"
    operation := "synthesis.electronics.voltage-source.v1"
    ports := [⟨"current", .input, .quantity .electronics .currentDim⟩,
      ⟨"delivered", .output, .quantity .electronics .power⟩]
    parameters := [⟨"electromotive-force", .voltage, s.emf.value⟩]
  }
  meaning x := x.delivered = s.delivered x.current
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

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

structure ThermalPoint where
  left : Thermal.Temperature
  right : Thermal.Temperature
  heatRate : Thermal.HeatRate

def thermalLink (g : Thermal.Link) : Primitive ThermalPoint where
  component := {
    name := "thermal-link"
    operation := "synthesis.thermal.conductance.v1"
    ports := [⟨"left", .input, .quantity .thermal .temperatureDim⟩,
      ⟨"right", .input, .quantity .thermal .temperatureDim⟩,
      ⟨"heat-rate", .output, .quantity .thermal .power⟩]
    parameters := [⟨"conductance", .thermalConductance, g.quantity.value⟩]
  }
  meaning x := x.heatRate = Thermal.heatRate g x.left x.right
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

theorem thermal_direction (g : Thermal.Link) :
    Verified (thermalLink g).model
      ⟨fun x => x.right.value ≤ x.left.value, fun x => 0 ≤ x.heatRate.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, ⟨0⟩, Thermal.heatRate g ⟨0⟩ ⟨0⟩⟩, rfl, Rat.le_refl⟩
  · intro x hx ha
    change 0 ≤ x.heatRate.value
    rw [hx]
    exact Thermal.hot_to_cold g x.left x.right ha

structure ElasticPoint where
  strain : Mechanics.Strain
  stress : Mechanics.Stress
  energyDensity : Quantity Rat Dimension.pressure

def elasticMaterial (material : Mechanics.ElasticMaterial) : Primitive ElasticPoint where
  component := {
    name := "elastic-material"
    operation := "synthesis.mechanics.linear-elastic.v1"
    ports := [⟨"strain", .input, .quantity (.custom "synthesis.mechanics") .scalar⟩,
      ⟨"stress", .output, .quantity (.custom "synthesis.mechanics") .pressure⟩,
      ⟨"energy-density", .output, .quantity (.custom "synthesis.mechanics") .pressure⟩]
    parameters := [⟨"young-modulus", .pressure, material.quantity.value⟩]
  }
  meaning x := x.stress = Mechanics.stress material x.strain ∧
    x.energyDensity = Mechanics.energyDensity material x.strain
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

theorem elastic_passive (material : Mechanics.ElasticMaterial) :
    Verified (elasticMaterial material).model ⟨fun _ => True, fun x => 0 ≤ x.energyDensity.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, Mechanics.stress material ⟨0⟩, Mechanics.energyDensity material ⟨0⟩⟩,
      ⟨rfl, rfl⟩, trivial⟩
  · intro x hx _
    change 0 ≤ x.energyDensity.value
    rw [hx.2]
    exact Mechanics.energy_nonnegative material x.strain

structure OpticalPoint where
  input : Photonics.OpticalPower
  transmitted : Quantity Rat Dimension.power
  reflected : Quantity Rat Dimension.power
  absorbed : Quantity Rat Dimension.power

def splitter (s : Photonics.Splitter) : Primitive OpticalPoint where
  component := {
    name := "splitter"
    operation := "synthesis.photonics.power-splitter.v1"
    ports := [⟨"input", .input, .quantity .photonics .power⟩,
      ⟨"transmitted", .output, .quantity .photonics .power⟩,
      ⟨"reflected", .output, .quantity .photonics .power⟩,
      ⟨"absorbed", .output, .quantity .photonics .power⟩]
    parameters := [⟨"transmittance", .scalar, s.transmittedFraction⟩,
      ⟨"reflectance", .scalar, s.reflectedFraction⟩]
  }
  meaning x := x.transmitted = Photonics.transmitted s x.input ∧
    x.reflected = Photonics.reflected s x.input ∧ x.absorbed = Photonics.absorbed s x.input
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

theorem optical_conservation (s : Photonics.Splitter) :
    Verified (splitter s).model ⟨fun _ => True, fun x =>
      x.transmitted.value + x.reflected.value + x.absorbed.value = x.input.quantity.value⟩ := by
  apply Primitive.verify
  · let input : Photonics.OpticalPower := ⟨⟨0⟩, Rat.le_refl⟩
    exact ⟨⟨input, Photonics.transmitted s input, Photonics.reflected s input, Photonics.absorbed s input⟩,
      ⟨rfl, rfl, rfl⟩, trivial⟩
  · intro x hx _
    change x.transmitted.value + x.reflected.value + x.absorbed.value = x.input.quantity.value
    rw [hx.1, hx.2.1, hx.2.2]
    exact Photonics.power_conservation s x.input

structure QuantumPoint where
  input : Quantum.Qubit
  output : Quantum.Qubit

/-- A finite operation catalog prevents attaching arbitrary maps to a recognized gate name. -/
inductive QuantumOperation where
  | x | z | phase

def QuantumOperation.gate : QuantumOperation → Quantum.Gate
  | .x => Quantum.x
  | .z => Quantum.z
  | .phase => Quantum.phase

def QuantumOperation.identifier : QuantumOperation → String
  | .x => "synthesis.quantum.x.v1"
  | .z => "synthesis.quantum.z.v1"
  | .phase => "synthesis.quantum.phase.v1"

def quantumGate (operation : QuantumOperation) : Primitive QuantumPoint where
  component := {
    name := "qubit-gate"
    operation := operation.identifier
    ports := [⟨"input", .input, .quantum 1⟩, ⟨"output", .output, .quantum 1⟩]
  }
  meaning x := x.output = operation.gate.run x.input
  valid := by cases operation <;> simp [IR.Technology.valid, IR.uniqueNames, QuantumOperation.identifier] <;> decide

theorem quantum_normalization (operation : QuantumOperation) :
    Verified (quantumGate operation).model
      ⟨fun x => x.input.Normalized, fun x => x.output.Normalized⟩ := by
  apply Primitive.verify
  · let input : Quantum.Qubit := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
    refine ⟨⟨input, operation.gate.run input⟩, rfl, ?_⟩
    simp [input, Quantum.Qubit.Normalized, Quantum.Qubit.normSquared, Quantum.Amplitude.normSquared] <;> grind
  · intro x hx ha
    change x.output.Normalized
    rw [hx]
    exact operation.gate.preserves_normalization x.input ha

structure ReactionPoint where
  before : List Chemistry.Water.Molecule
  after : List Chemistry.Water.Molecule

def waterFormation : Primitive ReactionPoint where
  component := {
    name := "water-formation"
    operation := "synthesis.chemistry.water-formation.v1"
    ports := [⟨"reactants", .input, .custom "synthesis.chemistry" "molecular-batch.v1"⟩,
      ⟨"products", .output, .custom "synthesis.chemistry" "molecular-batch.v1"⟩]
  }
  meaning x := Chemistry.Water.formation.Step x.before x.after
  valid := by simp [IR.Technology.valid, IR.uniqueNames] <;> decide

theorem water_atoms_conserved : Verified waterFormation.model ⟨fun _ => True, fun x =>
    ∀ element, Chemistry.inventory (fun species => Chemistry.Water.atoms species element) x.after =
      Chemistry.inventory (fun species => Chemistry.Water.atoms species element) x.before⟩ := by
  apply Primitive.verify
  · refine ⟨⟨Chemistry.Water.formation.reactants, Chemistry.Water.formation.products⟩, ?_, trivial⟩
    exact ⟨[], by simp, by simp⟩
  · intro x hx _ element
    exact Chemistry.Water.formation.conserves _ (Chemistry.Water.formation_balanced element)
      x.before x.after hx

end Synthesis.Domains.Components
