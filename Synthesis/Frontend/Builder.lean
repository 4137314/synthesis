import Synthesis.Frontend.Elaborate

namespace Synthesis.Frontend
set_option autoImplicit false

/-- A declaration program is distinct from its resulting canonical definition. Ordinary
Lean functions and extensible term syntax supply domain-specific declaration builders. -/
abbrev Builder := StateM IR.Definition Unit

def parameter (p : IR.Parameter) : Builder := modify fun d =>
  { d with parameters := d.parameters ++ [p] }
def port (p : IR.Port) : Builder := modify fun d => { d with ports := d.ports ++ [p] }
def instanceOf (name : Symbol) (definition : QualifiedId) (bindings : List IR.Binding := []) :
    Builder := modify fun d => { d with instances := d.instances ++ [⟨name, definition, bindings, [], {}⟩] }
def junction (name : Symbol) (contract : ContractId) (endpoints : List IR.Endpoint) : Builder :=
  modify fun d => { d with junctions := d.junctions ++ [⟨name, contract, endpoints, [], {}⟩] }
def operation (op : IR.Operation) : Builder := modify fun d =>
  { d with operations := d.operations ++ [op] }

def define (id : QualifiedId) (body : Builder) : IR.Definition :=
  (body.run { id := id }).2

/-- Reuse definitions explicitly; validation detects conflicting identities. -/
def design (root : IR.Definition) (library : List IR.Definition := []) : IR.Module :=
  { definitions := root :: library, root := root.id }

syntax "engineering " term " where " doSeq : term
macro_rules
  | `(engineering $id where $body:doSeq) =>
    `(Synthesis.Frontend.define $id (do $body))

end Synthesis.Frontend
