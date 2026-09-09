import Synthesis.IR.Diagnostic

namespace Synthesis.IR
set_option autoImplicit false
universe u

/-- Stable enumeration API. Declaration order is preserved, including malformed input.
The returned list is a snapshot; it does not promise the module's storage representation. -/
def Module.foldDefinitions {α : Type u} (m : Module) (initial : α)
    (visit : α → Definition → α) : α := m.definitions.foldl visit initial

def Module.findDefinition := Module.definition?

def Module.rootDefinition (m : Module) : Option Definition := m.findDefinition m.root

def Definition.foldPorts {α : Type u} (d : Definition) (initial : α)
    (visit : α → Port → α) : α := d.ports.foldl visit initial

def Definition.foldInstances {α : Type u} (d : Definition) (initial : α)
    (visit : α → Instance → α) : α := d.instances.foldl visit initial

def Definition.foldParameters {α : Type u} (d : Definition) (initial : α)
    (visit : α → Parameter → α) : α := d.parameters.foldl visit initial

def Definition.foldJunctions {α : Type u} (d : Definition) (initial : α)
    (visit : α → Junction → α) : α := d.junctions.foldl visit initial

def Definition.foldOperations {α : Type u} (d : Definition) (initial : α)
    (visit : α → Operation → α) : α := d.operations.foldl visit initial

/-- A traversal cursor pairs a stable address with a snapshot. -/
structure Cursor where
  reference : EntityRef
  entity : Entity
  deriving Repr

private def childCursor (r : EntityRef) (step : EntityStep) (e : Entity) : Cursor :=
  ⟨{ r with steps := r.steps ++ [step] }, e⟩

mutual
  private def walkOperation (r : EntityRef) (op : Operation) : List Cursor :=
    match op with
    | .node name _ args results _ body _ =>
      let here := childCursor r (.operation name) (.operation op)
      here :: ((args.zipIdx.map fun (t, n) => childCursor here.reference (.argument n) (.term t)) ++
        (results.map fun p => childCursor here.reference (.result p.name) (.parameter p)) ++
        walkOperations here.reference body)
  termination_by structural op

  private def walkOperations (r : EntityRef) (ops : List Operation) : List Cursor :=
    match ops with
    | [] => []
    | op :: rest => walkOperation r op ++ walkOperations r rest
  termination_by structural ops
end

private def walkDefinition (r : EntityRef) (d : Definition) : List Cursor :=
  ⟨r, .definition d⟩ ::
    ((d.parameters.map fun p => childCursor r (.parameter p.name) (.parameter p)) ++
    (d.ports.map fun p => childCursor r (.port p.name) (.port p)) ++
    (d.instances.flatMap fun i =>
      let here := childCursor r (.instance i.name) (.instance i)
      here :: i.bindings.map (fun b => childCursor here.reference (.binding b.name) (.binding b))) ++
    (d.junctions.map fun j => childCursor r (.junction j.name) (.junction j)) ++
    walkOperations r d.operations)

private def withAttributes (cursor : Cursor) : List Cursor :=
  cursor :: ((cursor.entity.attributes.zipIdx).map fun (a, n) =>
    let occurrence := ((cursor.entity.attributes.take n).filter (·.contract == a.contract)).length
    childCursor cursor.reference (.attribute a.contract occurrence) (.attribute a))

/-- Deterministic definition-table preorder, not expanded instance occurrences.
Within a definition: parameters, ports, instances/bindings, junctions, operations.
Nested operations use preorder; attributes immediately follow their owner. -/
def Module.walk (m : Module) : List Cursor :=
  ((⟨{}, .module m⟩ : Cursor) ::
    (m.bindings.map (fun b => childCursor {} (.binding b.name) (.binding b))) ++
    m.foldDefinitions ([] : List Cursor) (fun acc d => acc ++ walkDefinition { definition := some d.id } d))
    |>.flatMap withAttributes

/-- Filter contracts without knowing operation body storage. -/
def Module.operationsWith (m : Module) (contract : ContractId) : List Cursor :=
  m.walk.filter fun c => match c.entity with
    | .operation op => op.contract == contract
    | _ => false

/-- Expansion is explicitly budgeted, making cyclic or very large raw input safe to
inspect. Exhaustion is reported, never silently presented as a complete hierarchy. -/
def Module.walkHierarchy (m : Module) (budget : Nat) : Except (List Diagnostic) (List Cursor) := do
  let root ← match m.rootDefinition with
    | some d => .ok d
    | none => .error [Diagnostic.error "SYN-IR-UNRESOLVED-ENTITY" "Root definition is missing."]
  visit budget [] root
where
  visit : Nat → List Symbol → Definition → Except (List Diagnostic) (List Cursor)
    | 0, _, _ => .error [Diagnostic.error "SYN-IR-TRAVERSAL-LIMIT" "Hierarchy depth budget exhausted."]
    | fuel + 1, path, d => do
      let mut result := (walkDefinition { definition := some m.root, instances := path } d).flatMap withAttributes
      for i in d.instances do
        let child ← match m.findDefinition i.definition with
          | some child => .ok child
          | none => .error [Diagnostic.error "SYN-IR-UNRESOLVED-ENTITY" "Instance definition is missing."]
        result := result ++ (← visit fuel (path ++ [i.name]) child)
      pure result

/-- Structural categories describe the fixed substrate, never engineering domains. -/
inductive EntityKind where
  | module | definition | parameter | port | instance | junction | operation | term | attribute | binding
  deriving Repr, DecidableEq, BEq

def Entity.kind : Entity → EntityKind
  | .module _ => .module
  | .definition _ => .definition
  | .parameter _ => .parameter
  | .port _ => .port
  | .instance _ => .instance
  | .junction _ => .junction
  | .operation _ => .operation
  | .term _ => .term
  | .attribute _ => .attribute
  | .binding _ => .binding

def Entity.provenance : Entity → Provenance
  | .module m => m.provenance
  | .definition d => d.provenance
  | .instance i => i.provenance
  | .junction j => j.provenance
  | .operation (.node _ _ _ _ _ _ p) => p
  | _ => {}

def Module.entitiesOfKind (m : Module) (kind : EntityKind) : List Cursor :=
  m.walk.filter (fun c => c.entity.kind == kind)

/-- Locate declarations at a byte position; overlapping declarations are all returned
in traversal order. Stop positions are exclusive. Missing provenance is not guessed. -/
def Module.atSource (m : Module) (source : String) (offset : Nat) : List Cursor :=
  m.walk.filter fun c => c.entity.provenance.source.any fun span =>
    span.source == source && span.start ≤ offset && offset < span.stop

/-- Find reusable-definition references, independently of hierarchy expansion. -/
def Module.referencesToDefinition (m : Module) (id : QualifiedId) : List Cursor :=
  m.walk.filter fun c => match c.entity with
    | .instance i => i.definition == id
    | _ => false

end Synthesis.IR
