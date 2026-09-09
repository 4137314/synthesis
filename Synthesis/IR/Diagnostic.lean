import Synthesis.IR.Entity

namespace Synthesis.IR
set_option autoImplicit false

inductive Severity where
  | error | warning | note
  deriving Repr, DecidableEq, BEq

structure Diagnostic where
  code : ContractId
  severity : Severity := .error
  scope : Option QualifiedId := none
  entity : Option Symbol := none
  subject : Option EntityRef := none
  related : List EntityRef := []
  notes : List String := []
  source : Option SourceSpan := none
  message : String
  expected : Option Data := none
  actual : Option Data := none
  remediation : Option String := none
  deriving Repr, DecidableEq, BEq

def Diagnostic.error (code message : String) : Diagnostic :=
  { code := .named "synthesis.validation" code, message := message }

/-- Resolve with an actionable, machine-readable error; does not certify structure. -/
def Module.resolve (m : Module) (reference : EntityRef) :
    Except (List Diagnostic) (ResolvedEntity m) :=
  match h : m.findEntity reference with
  | some entity => .ok ⟨reference, entity, h⟩
  | none => .error [{ (Diagnostic.error "SYN-IR-UNRESOLVED-ENTITY"
      "Entity does not resolve in this module revision.") with
      subject := some reference,
      remediation := some "Check the definition, instance path and local declaration names." }]

end Synthesis.IR
