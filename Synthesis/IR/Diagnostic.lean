import Synthesis.IR.AST

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
  source : Option SourceSpan := none
  message : String
  expected : Option Data := none
  actual : Option Data := none
  remediation : Option String := none
  deriving Repr, DecidableEq, BEq

def Diagnostic.error (code message : String) : Diagnostic :=
  { code := .named "synthesis.validation" code, message := message }

end Synthesis.IR
