import Synthesis.Core.Parameter

namespace Synthesis.IR

/-- Domains are extensible without assigning any physical semantics to a name. -/
inductive Domain where
  | photonics | electronics | quantum | materials | thermal
  | custom (namespace_ : String)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Direction where
  | input | output
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Classical quantities and quantum resources must never be interchangeable. -/
inductive PortType where
  | quantity (domain : Domain) (dimension : Dimension)
  | quantum (registerWidth : Nat)
  | custom (namespace_ : String) (name : String)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Port where
  name : String
  direction : Direction
  type : PortType
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Operations identify an external semantic contract, never a backend instruction. -/
structure Component where
  name : String
  operation : String
  ports : List Port
  parameters : List Parameter := []
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Endpoint where
  component : String
  port : String
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Connection where
  source : Endpoint
  target : Endpoint
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Versioned backend-neutral technology graph. No implicit cross-domain coercions. -/
structure Technology where
  name : String
  components : List Component
  connections : List Connection
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def schemaVersion : Nat := 2

def Technology.port? (t : Technology) (e : Endpoint) : Option Port := do
  let c ← t.components.find? (·.name == e.component)
  c.ports.find? (·.name == e.port)

def uniqueNames (names : List String) : Bool :=
  names.all (fun n => !n.isEmpty) && names.eraseDups.length == names.length

def Connection.valid (t : Technology) (c : Connection) : Bool :=
  match t.port? c.source, t.port? c.target with
  | some s, some d => s.direction == .output && d.direction == .input && s.type == d.type
  | _, _ => false

/-- Structural validity only. Fan-out of quantum resources is rejected; no claim of
unitarity, conservation, realizability or physical correctness is made here. -/
def Technology.valid (t : Technology) : Bool :=
  !t.name.isEmpty && uniqueNames (t.components.map (·.name)) &&
  t.components.all (fun c => !c.operation.isEmpty && uniqueNames (c.ports.map (·.name)) &&
    uniqueNames (c.parameters.map (·.name)) &&
    c.ports.all (fun p => match p.type with
      | .quantum width => width > 0
      | .custom ns name => !ns.isEmpty && !name.isEmpty
      | .quantity (.custom ns) _ => !ns.isEmpty
      | _ => true)) &&
  t.connections.all (fun c => c.valid t) &&
  (t.connections.map (·.target)).eraseDups.length == t.connections.length &&
  t.connections.all (fun c => match t.port? c.source with
    | some ⟨_, _, .quantum _⟩ =>
      (t.connections.filter (·.source == c.source)).length == 1
    | _ => true)

/-- The boundary consumed by third-party backends. -/
structure Validated where
  ast : Technology
  structurallyValid : ast.valid = true

end Synthesis.IR
