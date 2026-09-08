import Synthesis.Frontend.Compile
import Synthesis.Semantics.Model

namespace Synthesis.Frontend

/-- Resolve semantic coverage before compilation. A caller must prove every component
and coupling is supported; physical requirement proofs are a separate `Verified` value. -/
def compileModel (design : Design) (semantics : Semantics.Interpretation α)
    (supported : semantics.Supported design.lower) : Except CompileError (Semantics.Model α) :=
  if h : design.lower.valid = true then
    .ok ⟨⟨design.lower, h⟩, semantics, supported⟩
  else .error .invalidStructure

theorem compileModel_preserves (design : Design) (semantics : Semantics.Interpretation α)
    (supported : semantics.Supported design.lower) (model : Semantics.Model α)
    (h : compileModel design semantics supported = .ok model) :
    model.graph.ast = design.lower ∧ model.interpretation = semantics := by
  unfold compileModel at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

end Synthesis.Frontend
