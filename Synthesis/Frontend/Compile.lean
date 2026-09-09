import Synthesis.IR.Extension

namespace Synthesis.Frontend
set_option autoImplicit false

abbrev CompileError := List IR.Diagnostic

/-- Structural compilation consumes explicit IR. Rich source elaboration is separate. -/
def compile := IR.validate

theorem compile_sound (source : IR.Module) (result : IR.Validated)
    (_h : compile source = .ok result) : result.ast.Structural := result.structurallyValid

theorem compile_preserves (source : IR.Module) (result : IR.Validated)
    (h : compile source = .ok result) : result.ast = source := by
  unfold compile IR.validate at h
  split at h
  · cases h; rfl
  · cases h

structure Certified (property : IR.Module → Prop) extends IR.Validated where
  satisfies : property ast

end Synthesis.Frontend
