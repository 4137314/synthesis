import Synthesis.Domains.Quantum
import Synthesis.Semantics.Primitive
import Synthesis.IR.Standard

namespace Synthesis.Domains.Components
open Physics Semantics
set_option autoImplicit false

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
  definition := {
    id := ⟨["synthesis.models", "qubit-gate"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.quantum" operation.identifier)]
    ports := [⟨"input", .named "synthesis.quantum" "resource", ⟨.named "synthesis.quantum" "qubit", []⟩, .named "synthesis.quantum" "consume", []⟩, ⟨"output", .named "synthesis.quantum" "resource", ⟨.named "synthesis.quantum" "qubit", []⟩, .named "synthesis.quantum" "produce", []⟩]
  }
  meaning x := x.output = operation.gate.run x.input
  valid := by cases operation <;> constructor <;> decide

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

end Synthesis.Domains.Components
