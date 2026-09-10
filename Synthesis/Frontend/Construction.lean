import Synthesis.Frontend.Builder
import Synthesis.Frontend.Scope

namespace Synthesis.Frontend
set_option autoImplicit false

/-- Transactional module construction. Failure returns diagnostics instead of a
partially mutated design. Explicit IDs make repeated builds reproducible. -/
abbrev DesignBuilder := StateT IR.Module (Except (List IR.Diagnostic))

/-- A declaration handle identifies its logical name; resolution against the final
snapshot is mandatory before it can serve as evidence. -/
structure DefinitionHandle where
  id : QualifiedId
  deriving Repr, DecidableEq

def DesignBuilder.addDefinition (definition : IR.Definition) : DesignBuilder DefinitionHandle := do
  let m ← get
  if (m.findDefinition definition.id).isSome then
    throw [{ (IR.Diagnostic.error "SYN-FRONTEND-DUPLICATE-DEFINITION"
      "A definition with this identity already exists.") with
      subject := some { definition := some definition.id } }]
  if !definition.identitiesValid then
    throw [{ (IR.Diagnostic.error "SYN-FRONTEND-INVALID-SCOPE"
      "Definition has empty, duplicate or shadowed member identities.") with
      subject := some { definition := some definition.id }, source := definition.provenance.source }]
  set { m with definitions := m.definitions ++ [definition] }
  pure ⟨definition.id⟩

/-- Reusable declaration programs remain the ergonomic definition-building layer.
Structural validity is checked once the entire library and root have been supplied. -/
def DesignBuilder.declare (id : QualifiedId) (body : Builder) : DesignBuilder DefinitionHandle :=
  DesignBuilder.addDefinition (define id body)

def DesignBuilder.finish (root : QualifiedId) (body : DesignBuilder Unit) :
    Except (List IR.Diagnostic) IR.Validated := do
  let (_, m) ← body.run { definitions := [], root := root }
  if h : m.Structural then pure ⟨m, h⟩ else throw m.diagnostics

end Synthesis.Frontend
