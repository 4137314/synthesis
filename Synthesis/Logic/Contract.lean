namespace Synthesis.Logic

/-- Observable behaviors may be states, traces, fields or histories. -/
abbrev Behavior (α : Type u) := α → Prop

/-- Assumptions remain explicit: a guarantee is required only in its operating envelope. -/
structure Contract (α : Type u) where
  assumption : Behavior α
  guarantee : Behavior α

namespace Contract

def Satisfies (behavior : Behavior α) (contract : Contract α) : Prop :=
  ∀ x, behavior x → contract.assumption x → contract.guarantee x

/-- A refinement accepts every environment of the specification and strengthens its
promise in those environments. -/
def Refines (implementation specification : Contract α) : Prop :=
  (∀ x, specification.assumption x → implementation.assumption x) ∧
  (∀ x, specification.assumption x → implementation.guarantee x → specification.guarantee x)

theorem refines_refl (c : Contract α) : c.Refines c :=
  ⟨fun _ h => h, fun _ _ h => h⟩

theorem refines_trans {a b c : Contract α}
    (hab : a.Refines b) (hbc : b.Refines c) : a.Refines c :=
  ⟨fun x h => hab.1 x (hbc.1 x h),
   fun x hc ha => hbc.2 x hc (hab.2 x (hbc.1 x hc) ha)⟩

theorem satisfies_of_refines {behavior : Behavior α} {a b : Contract α}
    (h : a.Refines b) (ha : Satisfies behavior a) : Satisfies behavior b :=
  fun x hx hb => h.2 x hb (ha x hx (h.1 x hb))

/-- Shared-observation composition. Compatibility is a separate proof obligation below. -/
def parallel (a b : Contract α) : Contract α :=
  ⟨fun x => a.assumption x ∧ b.assumption x,
   fun x => a.guarantee x ∧ b.guarantee x⟩

theorem parallel_sound {left right : Behavior α} {a b : Contract α}
    (ha : Satisfies left a) (hb : Satisfies right b) :
    Satisfies (fun x => left x ∧ right x) (a.parallel b) :=
  fun x hx h => ⟨ha x hx.1 h.1, hb x hx.2 h.2⟩

/-- Explicit compatibility: intersection must contain a behavior in the operating envelope.
This prevents accepting an impossible composition merely by vacuous implication. -/
structure Compatible (left right : Behavior α) (a b : Contract α) : Prop where
  witness : ∃ x, left x ∧ right x ∧ a.assumption x ∧ b.assumption x

end Contract
end Synthesis.Logic
