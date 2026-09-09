import Synthesis.IR.AST

namespace Synthesis.IR
set_option autoImplicit false

/-- Logical address steps. Only arguments and repeated attributes are positional;
those positions belong to the owning schema and must be remapped by transformations. -/
inductive EntityStep where
  | parameter (name : Symbol)
  | port (name : Symbol)
  | instance (name : Symbol)
  | junction (name : Symbol)
  | operation (name : Symbol)
  | result (name : Symbol)
  | argument (position : Nat)
  | attribute (contract : ContractId) (occurrence : Nat := 0)
  | binding (name : Symbol)
  deriving Repr, DecidableEq, BEq

/-- `definition = none` addresses the module. `instances` identifies an occurrence
below the selected definition (or root). `steps` addresses its local declarations.
Identity is relative to a module revision; edits require explicit trace remapping. -/
structure EntityRef where
  definition : Option QualifiedId := none
  instances : List Symbol := []
  steps : List EntityStep := []
  deriving Repr, DecidableEq, BEq

/-- Query results are snapshots, not mutable handles into canonical storage. -/
inductive Entity where
  | module (value : Module)
  | definition (value : Definition)
  | parameter (value : Parameter)
  | port (value : Port)
  | instance (value : Instance)
  | junction (value : Junction)
  | operation (value : Operation)
  | term (value : Term)
  | attribute (value : Attribute)
  | binding (value : Binding)
  deriving Repr, DecidableEq

def Operation.contract : Operation → ContractId
  | .node _ contract _ _ _ _ _ => contract

def Operation.arguments : Operation → List Term
  | .node _ _ args _ _ _ _ => args

def Operation.body : Operation → List Operation
  | .node _ _ _ _ _ body _ => body

def Entity.attributes : Entity → List Attribute
  | .module m => m.attributes
  | .definition d => d.attributes
  | .port p => p.attributes
  | .instance i => i.attributes
  | .junction j => j.attributes
  | .operation (.node _ _ _ _ attrs _ _) => attrs
  | _ => []

/-- One local lookup. Instance descent is explicit in EntityRef.instances. -/
def Entity.child? (entity : Entity) (step : EntityStep) : Option Entity :=
  match step, entity with
  | .attribute contract occurrence, e =>
    ((e.attributes.filter (·.contract == contract))[occurrence]?).map .attribute
  | .binding name, .module m => (m.bindings.find? (·.name == name)).map .binding
  | .binding name, .instance i => (i.bindings.find? (·.name == name)).map .binding
  | .parameter name, .definition d => (d.parameters.find? (·.name == name)).map .parameter
  | .port name, .definition d => (d.ports.find? (·.name == name)).map .port
  | .instance name, .definition d => (d.instances.find? (·.name == name)).map .instance
  | .junction name, .definition d => (d.junctions.find? (·.name == name)).map .junction
  | .operation name, .definition d => (d.operations.find? (·.name == name)).map .operation
  | .operation name, .operation op => (op.body.find? (·.name == name)).map .operation
  | .result name, .operation (.node _ _ _ results _ _ _) =>
    (results.find? (·.name == name)).map .parameter
  | .argument position, .operation op => (op.arguments[position]?).map .term
  | _, _ => none

def Entity.resolve? : Entity → List EntityStep → Option Entity
  | entity, [] => some entity
  | entity, step :: rest => do
    let next ← entity.child? step
    next.resolve? rest

/-- Total logical lookup, including finite paths through malformed cyclic input.
Use validated input when uniqueness and nonrecursive hierarchy are required. -/
def Module.findEntity (m : Module) (reference : EntityRef) : Option Entity := do
  let base : Entity ← match reference.definition, reference.instances with
    | none, [] => some (.module m)
    | id, path => do
      let d ← m.definition? (id.getD m.root)
      let scope ← m.descend? d path
      some (.definition scope)
  base.resolve? reference.steps

/-- A reference carries proof of resolution against this exact module snapshot. -/
structure ResolvedEntity (m : Module) where
  reference : EntityRef
  entity : Entity
  resolves : m.findEntity reference = some entity

end Synthesis.IR
