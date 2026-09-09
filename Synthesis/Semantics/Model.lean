import Synthesis.IR.Extension
import Synthesis.Logic.Contract

namespace Synthesis.Semantics
open Logic
set_option autoImplicit false
universe u v
variable {α : Type u} {β : Type v}

/-- An interpreter must cover the complete module, including bindings, attributes,
junctions and behavior bodies. Unknown constructs return `none`. -/
structure Interpretation (Observation : Type u) where
  meaning : IR.Module → Option (Behavior Observation)

def Interpretation.Supported (i : Interpretation α) (m : IR.Module) : Prop :=
  ∃ b, i.meaning m = some b

def Interpretation.Meaning (i : Interpretation α) (m : IR.Module) : Behavior α :=
  fun x => ∃ b, i.meaning m = some b ∧ b x

/-- Local state and interface spaces need not be the global observation type. -/
structure LocalRelation (Global : Type u) where
  Local : Type v
  observe : Global → Local
  relation : Behavior Local

def LocalRelation.behavior (part : LocalRelation.{u,v} α) : Behavior α :=
  fun x => part.relation (part.observe x)

/-- Composition is conjunction of pulled-back local relations. Feasibility is separate. -/
def assemble (parts : List (LocalRelation.{u,v} α)) : Behavior α :=
  fun x => ∀ part ∈ parts, part.behavior x

structure Model (Observation : Type u) where
  graph : IR.Validated
  interpretation : Interpretation Observation
  supported : interpretation.Supported graph.ast

def Model.behavior (model : Model α) : Behavior α :=
  model.interpretation.Meaning model.graph.ast

structure Verified (model : Model α) (requirement : Contract α) : Prop where
  feasible : ∃ x, model.behavior x ∧ requirement.assumption x
  correct : Contract.Satisfies model.behavior requirement

/-- Exact endomorphisms are a convenience specialization of the general transformation API. -/
structure PreservingPass (Observation : Type u) where
  run : Model Observation → Model Observation
  preserves : ∀ model x, (run model).behavior x ↔ model.behavior x

def PreservingPass.identity : PreservingPass α := ⟨id, fun _ _ => Iff.rfl⟩
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

theorem unsupported {i : Interpretation α} {m : IR.Module}
    (missing : i.meaning m = none) (x : α) : ¬i.Meaning m x := by
  rintro ⟨b, found, _⟩
  rw [missing] at found
  cases found

end Synthesis.Semantics
