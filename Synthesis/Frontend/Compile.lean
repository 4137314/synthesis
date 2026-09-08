import Synthesis.IR.AST

namespace Synthesis.Frontend

/-- The initial frontend is an embedded Lean DSL. Future surface languages lower here. -/
structure Design where
  name : String
  components : List IR.Component := []
  connections : List IR.Connection := []
  deriving Repr

def Design.lower (d : Design) : IR.Technology :=
  ⟨d.name, d.components, d.connections⟩

inductive CompileError where
  | invalidStructure
  deriving Repr, BEq

/-- Fail closed: invalid designs cannot cross the validated AST boundary. -/
def compile (d : Design) : Except CompileError IR.Validated :=
  if h : d.lower.valid = true then .ok ⟨d.lower, h⟩
  else .error .invalidStructure

theorem compile_sound (d : Design) (result : IR.Validated)
    (_h : compile d = .ok result) : result.ast.valid = true :=
  result.structurallyValid

theorem compile_preserves (d : Design) (result : IR.Validated)
    (h : compile d = .ok result) : result.ast = d.lower := by
  unfold compile at h
  split at h
  · cases h
    rfl
  · cases h

/-- Physical models supply their own predicates and proofs, separately from compilation. -/
structure Certified (physicalLaw : IR.Technology → Prop) extends IR.Validated where
  satisfies : physicalLaw ast

end Synthesis.Frontend
