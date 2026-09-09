import Synthesis

namespace Synthesis.Examples.Assurance
open Logic Physics Semantics Systems
set_option autoImplicit false

def inventoryDimension : Dimension := { mass := 1 }
structure Inventory where
  before : Quantity Int inventoryDimension
  after : Quantity Int inventoryDimension

def balance (x : Inventory) : Balance Int inventoryDimension :=
  ⟨x.before, x.after, ⟨0⟩, ⟨0⟩, ⟨0⟩⟩

def storage : Primitive Inventory where
  definition := {
    id := ⟨["synthesis.examples", "inventory"]⟩
    operations := [IR.Standard.relation "conservation" (.named "synthesis.examples" "closed-inventory")]
  }
  meaning x := (balance x).Holds
  valid := by constructor <;> decide

def model := storage.model

def conserved : Contract Inventory := ⟨fun _ => True, fun x => x.after = x.before⟩

theorem inventory_verified : Verified model conserved := by
  apply Primitive.verify
  · exact ⟨⟨⟨4⟩, ⟨4⟩⟩, rfl, trivial⟩
  · intro x hx _
    exact Balance.closed_conserves hx rfl rfl rfl

/-- Rich source, inspectable lowering, retained requirement and explicit denotation. -/
def design : Design.Model Unit Inventory where
  source := ()
  lower _ := storage.ir
  behavior _ := storage.meaning
  interpretation := model.interpretation
  represented := storage.behavior_iff
  supported := model.supported
  requirements := [⟨.named "synthesis.examples" "inventory-conserved", conserved,
    IR.Standard.relation "conservation" (.named "synthesis.examples" "closed-inventory"), {}⟩]
  requirementsRetained := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨storage.definition, by simp [Primitive.ir], by simp [storage]⟩

/-- Semantic coverage does not imply feasibility. -/
def impossible : Primitive Unit where
  definition := storage.definition
  meaning _ := False
  valid := storage.valid

example : ¬Verified impossible.model ⟨fun _ => True, fun _ => True⟩ := by
  intro proof
  obtain ⟨x, hx, _⟩ := proof.feasible
  exact (impossible.behavior_iff x).mp hx

/-- A bounded discrete controller remains independent of the compiler representation. -/
def boundedInventory (capacity : Nat) : TransitionSystem Nat where
  initial s := s = 0
  step s t := t = s ∨ (s < capacity ∧ t = s + 1) ∨ (0 < s ∧ t = s - 1)

theorem bounded_invariant (capacity : Nat) :
    Invariant (boundedInventory capacity) (fun s => s ≤ capacity) := by
  constructor
  · intro s hs
    simp [boundedInventory] at hs
    omega
  · intro s t hs hstep
    simp only [boundedInventory] at hstep
    omega

theorem reachable_within_capacity (capacity s : Nat)
    (reachable : Reachable (boundedInventory capacity) s) : s ≤ capacity :=
  (bounded_invariant capacity).reachable reachable

example (first second : PreservingPass Inventory) :
    Verified ((first.andThen second).run model) conserved :=
  (first.andThen second).verified inventory_verified

/-- The semantic DSL composes typed models, not untyped component records. -/
def pairedInventory : Design.System (Inventory × Inventory) :=
  engineering_system ⟨["synthesis.examples", "paired-inventory"]⟩ where
    Frontend.place "left" model Prod.fst
    Frontend.place "right" model Prod.snd
    Frontend.constrain (IR.Standard.relation "initial-agreement"
      (.named "synthesis.examples" "inventory-initial-agreement"))
      (fun x => x.1.before = x.2.before)

example : (Frontend.compileSystem pairedInventory).isOk = true := by decide

-- Two placements share the original definition: root, two wrappers, one inventory definition.
example : pairedInventory.lower.definitions.length = 4 := by decide

example (compiled : Semantics.Model (Inventory × Inventory))
    (h : Frontend.compileSystem pairedInventory = .ok compiled) :
    ∀ x, compiled.behavior x ↔ pairedInventory.behavior x :=
  Frontend.compileSystem_preserves pairedInventory compiled h

end Synthesis.Examples.Assurance
