import Synthesis.Semantics.Model

namespace Synthesis.Semantics
set_option autoImplicit false
universe u
variable {Observation : Type u}

/-- A domain primitive binds a complete parameterized interface to its mathematical
relation. It is a single-node frontend model, not a target instruction. -/
structure Primitive (Observation : Type u) where
  component : IR.Component
  meaning : Logic.Behavior Observation
  valid : (IR.Technology.mk component.name [component] []).valid = true

def Primitive.model (primitive : Primitive Observation) : Model Observation where
  graph := ⟨⟨primitive.component.name, [primitive.component], []⟩, primitive.valid⟩
  interpretation := {
    component := fun c => if c = primitive.component then some primitive.meaning else none
    connection := fun _ => none
  }
  supported := by
    constructor
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst c
      exact ⟨primitive.meaning, by simp⟩
    · simp

theorem Primitive.behavior_iff (primitive : Primitive Observation) (x : Observation) :
    primitive.model.behavior x ↔ primitive.meaning x := by
  simp [Model.behavior, Interpretation.Meaning, model]

theorem Primitive.verify (primitive : Primitive Observation) (requirement : Logic.Contract Observation)
    (feasible : ∃ x, primitive.meaning x ∧ requirement.assumption x)
    (correct : Logic.Contract.Satisfies primitive.meaning requirement) :
    Verified primitive.model requirement := by
  constructor
  · obtain ⟨x, hx, ha⟩ := feasible
    exact ⟨x, (primitive.behavior_iff x).mpr hx, ha⟩
  · intro x hx ha
    exact correct x ((primitive.behavior_iff x).mp hx) ha

end Synthesis.Semantics
