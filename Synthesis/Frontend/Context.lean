import Synthesis.Frontend.Scope
import Synthesis.IR.Composition
import Synthesis.IR.Index

namespace Synthesis.Frontend
set_option autoImplicit false

/-- Human names bind to semantic locators; display aliases are never entity identity. -/
structure NameBinding where
  name : QualifiedId
  entity : IR.EntityRef
  source : Option IR.SourceSpan := none

/-- Explicit reusable elaboration context, separate from canonical schema storage.
Scopes are innermost first. The nearest scope shadows outer scopes; duplicates in
that scope are ambiguous. Extensions remain caller-supplied pure configuration. -/
structure ElaborationContext where
  module : IR.Module
  definition : QualifiedId
  instances : List Symbol := []
  scopes : List (List NameBinding) := []
  parameters : IR.Context := []
  expected : Option IR.TypeExpr := none
  extensions : IR.ExtensionSet
  source : Option SourceDocument := none
  generatedBy : Option ContractId := none

private def candidates (name : QualifiedId) : List (List NameBinding) → List NameBinding
  | [] => []
  | scope :: rest =>
    let found := scope.filter (·.name == name)
    if found.isEmpty then candidates name rest else found

def ElaborationContext.resolveName (context : ElaborationContext) (name : QualifiedId) :
    Except (List IR.Diagnostic) (IR.ResolvedEntity context.module) :=
  match candidates name context.scopes with
  | [] => .error [{ (IR.Diagnostic.error "SYN-FRONTEND-UNRESOLVED-NAME"
      "No binding for the requested name in the active scopes.") with
      actual := some (.sequence (name.segments.map IR.Data.text)) }]
  | [binding] => context.module.resolve binding.entity
  | bindings => .error [{ (IR.Diagnostic.error "SYN-FRONTEND-AMBIGUOUS-NAME"
      "Multiple declarations bind this name in the nearest scope.") with
      related := bindings.map (·.entity), source := bindings.head?.bind (·.source),
      remediation := some "Use an unambiguous qualified alias or remove the duplicate binding." }]

/-- Expected-type propagation returns checked inference results or structured mismatch
information. It does not execute or numerically approximate symbolic expressions. -/
def ElaborationContext.infer (context : ElaborationContext) (term : IR.Term) :
    Except (List IR.Diagnostic) IR.TypeExpr :=
  match context.extensions.extension.infer context.parameters term with
  | none => .error [IR.Diagnostic.error "SYN-FRONTEND-UNSUPPORTED-TERM"
      "Term has an unresolved variable or unsupported contract/signature."]
  | some actual =>
    if context.expected.any (· != actual) then
      .error [{ (IR.Diagnostic.error "SYN-FRONTEND-TYPE-MISMATCH" "Inferred type differs from the expected type.") with
        expected := context.expected.map (fun t => .tagged t.constructor t.arguments),
        actual := some (.tagged actual.constructor actual.arguments) }]
    else .ok actual

/-- Resolve reusable definition targets for IDE navigation without inspecting storage. -/
def definitionOf (m : IR.Module) (reference : IR.EntityRef) : Option IR.EntityRef := do
  let entity ← m.findEntity reference
  match entity with
  | .instance i => some { definition := some i.definition }
  | .definition d => some { definition := some d.id }
  | _ => do
    let scope ← m.findEntity { reference with steps := [] }
    match scope with
    | .definition d => some { definition := some d.id }
    | _ => none

end Synthesis.Frontend
