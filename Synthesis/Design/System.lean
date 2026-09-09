import Synthesis.Design.Model

namespace Synthesis.Design
set_option autoImplicit false
universe u

/-- A component retains its own typed observation space and already covered model. -/
structure Part (Global : Type u) where
  name : Symbol
  Local : Type u
  model : Semantics.Model Local
  observe : Global → Local

/-- A coupling supplies an explicit relation; a junction label alone supplies none. -/
structure Coupling (Global : Type u) where
  junction : IR.Junction
  relation : Logic.Behavior Global

/-- A relational law with an explicit compiler-facing declaration. -/
structure Constraint (Global : Type u) where
  declaration : IR.Operation
  relation : Logic.Behavior Global

/-- Rich hierarchical composition. Feasibility of the conjunction is a separate obligation. -/
structure System (Global : Type u) where
  id : QualifiedId
  parts : List (Part Global) := []
  couplings : List (Coupling Global) := []
  requirements : List (Requirement Global) := []
  constraints : List (Constraint Global) := []
  provenance : IR.Provenance := {}

def Part.wrapperId {Global : Type u} (system : System Global) (part : Part Global) : QualifiedId :=
  ⟨system.id.segments ++ [part.name.text]⟩

/-- The wrapper retains child-module attributes, annotations, provenance and root bindings.
An inner instance avoids conflating module metadata with the child root definition. -/
def Part.wrapper {Global : Type u} (system : System Global) (part : Part Global) : IR.Definition := {
  id := part.wrapperId system
  instances := [⟨"body", part.model.graph.ast.root, part.model.graph.ast.bindings, [], {}⟩]
  attributes := part.model.graph.ast.attributes
  annotations := part.model.graph.ast.annotations
  provenance := part.model.graph.ast.provenance }

def System.rootDefinition {Global : Type u} (system : System Global) : IR.Definition := {
  id := system.id
  instances := system.parts.map fun part => ⟨part.name, part.wrapperId system, [], [], {}⟩
  junctions := system.couplings.map (·.junction)
  operations := system.constraints.map (·.declaration) ++ system.requirements.map (·.declaration)
  provenance := system.provenance }

/-- Identical definitions are shared. Conflicting definitions with the same ID are
retained for validation to reject, never silently replaced by one another. -/
def System.lower {Global : Type u} (system : System Global) : IR.Module := {
  definitions := system.rootDefinition ::
    ((system.parts.map (fun part => part.wrapper system)) ++
      system.parts.flatMap (fun part => part.model.graph.ast.definitions)).eraseDups
  root := system.id
  provenance := system.provenance }

def System.behavior {Global : Type u} (system : System Global) : Logic.Behavior Global :=
  fun x => (∀ part ∈ system.parts, part.model.behavior (part.observe x)) ∧
    (∀ coupling ∈ system.couplings, coupling.relation x) ∧
    (∀ constraint ∈ system.constraints, constraint.relation x)

/-- Source composition provides the interpretation. An altered module has no coverage
from this construction; an independent consumer must supply its own dialect interpretation. -/
def System.represented {Global : Type u} (system : System Global) : Model (System Global) Global where
  source := system
  lower := System.lower
  behavior := System.behavior
  interpretation := ⟨fun m => if m = system.lower then some system.behavior else none⟩
  represented := fun _ => by simp [Semantics.Interpretation.Meaning]
  supported := ⟨system.behavior, by simp⟩
  requirements := system.requirements
  requirementsRetained := by
    intro r hr
    exact ⟨system.rootDefinition, by simp [System.lower],
      List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)⟩

/-- A source component's endpoint, including the explicit module-boundary wrapper. -/
def endpoint (part : Symbol) (port : Symbol) (path : List Symbol := []) : IR.Endpoint :=
  ⟨part :: "body" :: path, port⟩

end Synthesis.Design
