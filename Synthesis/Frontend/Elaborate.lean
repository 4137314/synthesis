import Synthesis.Frontend.Compile
import Synthesis.Design.Model

namespace Synthesis.Frontend
set_option autoImplicit false
universe u v
variable {Source : Type u} {Observation : Type v}

/-- The source-to-IR denotation proof remains kernel checked. -/
def compileModel (design : Design.Model Source Observation) :
    Except CompileError (Semantics.Model Observation) :=
  if h : (design.lower design.source).Structural then
    .ok ⟨⟨design.lower design.source, h⟩, design.interpretation, design.supported⟩
  else .error (design.lower design.source).diagnostics

theorem compileModel_preserves (design : Design.Model Source Observation)
    (model : Semantics.Model Observation) (h : compileModel design = .ok model) :
    ∀ x, model.behavior x ↔ design.behavior design.source x := by
  unfold compileModel at h
  split at h
  · cases h
    exact design.represented
  · cases h

end Synthesis.Frontend
