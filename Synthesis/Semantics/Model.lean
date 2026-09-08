import Synthesis.IR.AST
import Synthesis.Logic.Contract

namespace Synthesis.Semantics
open Logic

/-- A domain package interprets full components, including their interface. `none`
means unsupported, not an unconstrained component. Both operations and couplings
must be interpreted; a connection is never silently assigned physical semantics. -/
structure Interpretation (Observation : Type u) where
  component : IR.Component → Option (Behavior Observation)
  connection : IR.Connection → Option (Behavior Observation)

def Interpretation.Supported (semantics : Interpretation α) (ast : IR.Technology) : Prop :=
  (∀ c ∈ ast.components, ∃ meaning, semantics.component c = some meaning) ∧
  (∀ c ∈ ast.connections, ∃ meaning, semantics.connection c = some meaning)

/-- Existential lookup makes an unsupported operation denote no behavior. -/
def Interpretation.Meaning (semantics : Interpretation α) (ast : IR.Technology) : Behavior α :=
  fun x =>
    (∀ c ∈ ast.components, ∃ meaning, semantics.component c = some meaning ∧ meaning x) ∧
    (∀ c ∈ ast.connections, ∃ meaning, semantics.connection c = some meaning ∧ meaning x)

structure Model (Observation : Type u) where
  graph : IR.Validated
  interpretation : Interpretation Observation
  supported : interpretation.Supported graph.ast

def Model.behavior (model : Model α) : Behavior α :=
  model.interpretation.Meaning model.graph.ast

/-- Evidence belongs to a particular graph, interpretation and operating envelope.
Feasibility rules out empty semantics, but is not universal input realizability. -/
structure Verified (model : Model α) (requirement : Contract α) : Prop where
  feasible : ∃ x, model.behavior x ∧ requirement.assumption x
  correct : Contract.Satisfies model.behavior requirement

/-- A compiler transformation carries a behavior-preservation obligation. Structural
validity alone is insufficient. Equality also preserves feasibility. -/
structure PreservingPass (Observation : Type u) where
  run : Model Observation → Model Observation
  preserves : ∀ model x, (run model).behavior x ↔ model.behavior x

def PreservingPass.identity : PreservingPass α :=
  ⟨id, fun _ _ => Iff.rfl⟩

def PreservingPass.andThen (first second : PreservingPass α) : PreservingPass α :=
  ⟨fun model => second.run (first.run model),
   fun model x => (second.preserves (first.run model) x).trans (first.preserves model x)⟩

theorem PreservingPass.verified (pass : PreservingPass α) {model : Model α}
    {requirement : Contract α} (proof : Verified model requirement) :
    Verified (pass.run model) requirement := by
  constructor
  · obtain ⟨x, hx, ha⟩ := proof.feasible
    exact ⟨x, (pass.preserves model x).mpr hx, ha⟩
  · intro x hx ha
    exact proof.correct x ((pass.preserves model x).mp hx) ha

/-- Missing semantics cannot accidentally yield an accepted behavior. -/
theorem unsupported_component {semantics : Interpretation α} {ast : IR.Technology}
    {component : IR.Component} (member : component ∈ ast.components)
    (missing : semantics.component component = none) :
    ∀ x, ¬semantics.Meaning ast x := by
  intro x h
  obtain ⟨meaning, found, _⟩ := h.1 component member
  rw [missing] at found
  cases found

end Synthesis.Semantics
