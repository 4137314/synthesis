import Synthesis.IR.Query
import Synthesis.IR.WellFormed

namespace Synthesis.IR
set_option autoImplicit false

/-- Rebuildable definition index. The array is an implementation detail, not portable
IR. `agrees` prevents attaching a stale cache to a changed source. -/
structure Index (source : Module) where
  private entries : Array Definition
  private agrees : entries.toList = source.definitions

/-- Index construction requires unique, structurally valid declarations. -/
def Module.index (m : Module) : Except (List Diagnostic) (Index m) :=
  if m.Structural then .ok ⟨m.definitions.toArray, by simp⟩
  else .error m.diagnostics

/-- The initial index uses contiguous storage. Consumers depend on lookup semantics,
not this implementation; a tree/hash implementation can replace it with the same law. -/
def Index.findDefinition {m : Module} (index : Index m) (id : QualifiedId) : Option Definition :=
  index.entries.toList.find? (·.id == id)

@[simp] theorem Index.findDefinition_eq {m : Module} (index : Index m) (id : QualifiedId) :
    index.findDefinition id = m.findDefinition id := by
  simp [Index.findDefinition, index.agrees, Module.findDefinition, Module.definition?]

end Synthesis.IR
