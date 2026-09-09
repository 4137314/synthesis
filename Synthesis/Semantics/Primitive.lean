import Synthesis.Semantics.Model

namespace Synthesis.Semantics
set_option autoImplicit false
universe u
variable {Observation : Type u}

/-- A single reusable definition and its complete relational model. -/
structure Primitive (Observation : Type u) where
  definition : IR.Definition
  meaning : Logic.Behavior Observation
  valid : ({ definitions := [definition], root := definition.id } : IR.Module).Structural

def Primitive.ir (p : Primitive Observation) : IR.Module :=
  { definitions := [p.definition], root := p.definition.id }

def Primitive.model (p : Primitive Observation) : Model Observation where
  graph := ⟨p.ir, p.valid⟩
  interpretation := ⟨fun m => if m = p.ir then some p.meaning else none⟩
  supported := ⟨p.meaning, by simp⟩

theorem Primitive.behavior_iff (p : Primitive Observation) (x : Observation) :
    p.model.behavior x ↔ p.meaning x := by
  simp [Model.behavior, Interpretation.Meaning, model]

theorem Primitive.verify (p : Primitive Observation) (requirement : Logic.Contract Observation)
    (feasible : ∃ x, p.meaning x ∧ requirement.assumption x)
    (correct : Logic.Contract.Satisfies p.meaning requirement) :
    Verified p.model requirement := by
  constructor
  · obtain ⟨x, hx, ha⟩ := feasible
    exact ⟨x, (p.behavior_iff x).mpr hx, ha⟩
  · intro x hx ha
    exact correct x ((p.behavior_iff x).mp hx) ha

end Synthesis.Semantics
