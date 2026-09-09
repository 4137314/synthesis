import Synthesis.IR.Value

namespace Synthesis.IR
set_option autoImplicit false

/-- Extension-defined roles include source/sink, oriented terminals and owned resources. -/
structure Port where
  name : Symbol
  interface : ContractId
  type : TypeExpr
  role : ContractId
  attributes : List Attribute := []
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Empty path addresses the containing definition's external interface. -/
structure Endpoint where
  path : List Symbol
  port : Symbol
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- A connector contract owns multiway laws and incidence/ownership restrictions. -/
structure Junction where
  name : Symbol
  contract : ContractId
  endpoints : List Endpoint
  attributes : List Attribute := []
  provenance : Provenance := {}
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Lexically scoped bodies support relations, dynamics, algorithms and domain structures.
There is no implicit evaluation, causality, derivative or physical meaning. -/
inductive Operation where
  | node (name : Symbol) (contract : ContractId) (arguments : List Term)
      (results : List Parameter) (attributes : List Attribute)
      (body : List Operation) (provenance : Provenance)
  deriving Repr

mutual
  def Operation.decEq (a b : Operation) : Decidable (a = b) :=
    match a, b with
    | .node a0 a1 a2 a3 a4 a5 a6, .node b0 b1 b2 b3 b4 b5 b6 =>
      haveI := Operation.listDecEq a5 b5
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6) (by simp)
  termination_by structural a

  def Operation.listDecEq (a b : List Operation) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      haveI := Operation.decEq x y
      haveI := Operation.listDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
  termination_by structural a
end

instance : DecidableEq Operation := Operation.decEq


def Operation.name : Operation → Symbol
  | .node name _ _ _ _ _ _ => name

structure Instance where
  name : Symbol
  definition : QualifiedId
  bindings : List Binding := []
  attributes : List Attribute := []
  provenance : Provenance := {}
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Reusable structure, with local parameters, state/behavior bodies and external ports. -/
structure Definition where
  id : QualifiedId
  parameters : List Parameter := []
  ports : List Port := []
  instances : List Instance := []
  junctions : List Junction := []
  operations : List Operation := []
  attributes : List Attribute := []
  annotations : List Annotation := []
  provenance : Provenance := {}
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Canonical interchange container. Definitions are stored once, instances bind them. -/
structure Module where
  definitions : List Definition
  root : QualifiedId
  bindings : List Binding := []
  attributes : List Attribute := []
  annotations : List Annotation := []
  provenance : Provenance := {}
  schema : Nat := 3
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def schemaVersion : Nat := 3

def Module.definition? (m : Module) (id : QualifiedId) : Option Definition :=
  m.definitions.find? (·.id == id)

/-- Resolution consumes a typed path; no textual concatenation or global registration. -/
def Module.descend? (m : Module) (d : Definition) : List Symbol → Option Definition
  | [] => some d
  | name :: rest => do
    let inst ← d.instances.find? (·.name == name)
    let child ← m.definition? inst.definition
    m.descend? child rest

def Module.port? (m : Module) (d : Definition) (e : Endpoint) : Option Port := do
  let scope ← m.descend? d e.path
  scope.ports.find? (·.name == e.port)

/-- A resolved reference is tied to this module and scope, not reusable on changed IR. -/
structure ResolvedEndpoint (m : Module) (d : Definition) where
  reference : Endpoint
  port : Port
  resolves : m.port? d reference = some port

end Synthesis.IR
