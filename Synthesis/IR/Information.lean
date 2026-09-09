import Synthesis.IR.Extension

namespace Synthesis.IR
set_option autoImplicit false

/-- Ground applications are not necessarily evaluated values. A literal requirement
must not mistake a symbolic application for a concrete coefficient. -/
def Term.isLiteral : Term → Bool
  | .literal _ _ => true
  | _ => false

def concreteBindings (parameters : List Parameter) (bindings : List Binding) : Bool :=
  parameters.all fun p => match bindings.find? (·.name == p.name) with
    | some b => b.value.isLiteral
    | none => match p.value with
      | some value => value.isLiteral
      | none => false

/-- Conservative information check: every occurrence has literal parameters. Derived
expressions require an explicit evaluation/specialization stage before passing it. -/
def Module.concreteParameters (m : Module) : Bool :=
  (match m.definition? m.root with
   | none => false
   | some root => concreteBindings root.parameters m.bindings) &&
  m.definitions.all (fun d => d.instances.all fun i =>
    match m.definition? i.definition with
    | none => false
    | some child => concreteBindings child.parameters i.bindings)

structure Specialized (ext : Extension) extends Checked ext where
  concrete : ast.concreteParameters = true

end Synthesis.IR
