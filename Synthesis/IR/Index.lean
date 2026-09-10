import Synthesis.IR.Query
import Synthesis.IR.WellFormed
import Std.Data.HashMap.Lemmas

namespace Synthesis.IR
set_option autoImplicit false

private def indexDefinitions (definitions : List Definition) : Std.HashMap QualifiedId Definition :=
  definitions.foldr (fun d index => index.insert d.id d) ∅

private theorem indexDefinitions_agrees (definitions : List Definition) (id : QualifiedId) :
    (indexDefinitions definitions)[id]? = definitions.find? (·.id == id) := by
  induction definitions with
  | nil => simp [indexDefinitions]
  | cons d rest ih =>
    simp only [indexDefinitions, List.foldr_cons, Std.HashMap.getElem?_insert, List.find?_cons]
    by_cases h : d.id = id
    · simp [h]
    · have hb : (d.id == id) = false := by simp [h]
      simp [hb, ← ih, indexDefinitions]

/-- Derived hash index, never canonical truth. The correspondence proof also covers
raw duplicate IDs with the canonical query's first-declaration-wins behavior. -/
structure Index (source : Module) where
  private entries : Std.HashMap QualifiedId Definition
  private agrees : ∀ id, entries[id]? = source.findDefinition id

/-- Build an index without claiming validation. Useful for already validated sources
and bounded raw tooling; it never promotes malformed IR to Validated. -/
def Module.buildIndex (m : Module) : Index m :=
  ⟨indexDefinitions m.definitions, fun id => indexDefinitions_agrees m.definitions id⟩

/-- Validate once when a consumer requires structural assurance before indexing. -/
def Module.index (m : Module) : Except (List Diagnostic) (Index m) :=
  if m.Structural then .ok m.buildIndex else .error m.diagnostics

/-- Expected constant-time lookup; public iteration still uses canonical query order. -/
def Index.findDefinition {m : Module} (index : Index m) (id : QualifiedId) : Option Definition :=
  index.entries[id]?

@[simp] theorem Index.findDefinition_eq {m : Module} (index : Index m) (id : QualifiedId) :
    index.findDefinition id = m.findDefinition id := index.agrees id

/-- Hierarchical resolution uses indexed definition lookup at each path step. -/
def Index.descend? {m : Module} (index : Index m) (d : Definition) : List Symbol → Option Definition
  | [] => some d
  | name :: rest => do
    let instance_ ← d.instances.find? (·.name == name)
    let child ← index.findDefinition instance_.definition
    index.descend? child rest

theorem Index.descend?_eq {m : Module} (index : Index m) (d : Definition) (path : List Symbol) :
    index.descend? d path = m.descend? d path := by
  induction path generalizing d with
  | nil => rfl
  | cons name rest ih => simp [Index.descend?, Module.descend?, Index.findDefinition_eq,
      Module.findDefinition, ih]

/-- Entity resolution reuses the definition hash table and preserves local query rules. -/
def Index.findEntity {m : Module} (index : Index m) (reference : EntityRef) : Option Entity := do
  let base : Entity ← match reference.definition, reference.instances with
    | none, [] => some (.module m)
    | id, path => do
      let d ← index.findDefinition (id.getD m.root)
      let scope ← index.descend? d path
      some (.definition scope)
  base.resolve? reference.steps

@[simp] theorem Index.findEntity_eq {m : Module} (index : Index m) (reference : EntityRef) :
    index.findEntity reference = m.findEntity reference := by
  simp only [Index.findEntity, Module.findEntity, Index.findDefinition_eq,
    Module.findDefinition, Index.descend?_eq]
  rfl

end Synthesis.IR
