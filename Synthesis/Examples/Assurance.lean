import Synthesis

namespace Synthesis.Examples.Assurance
open Logic Physics Semantics Systems

/-- Abstract conserved inventory. Exact integer semantics are a deliberate modeling
choice, not a continuous thermodynamic model. -/
def inventoryDimension : Dimension := { mass := 1 }

structure Inventory where
  before : Quantity Int inventoryDimension
  after : Quantity Int inventoryDimension

def storage : IR.Component := ⟨"inventory", "synthesis.examples.closed-inventory.v1", [], []⟩

def design : Frontend.Design := {
  name := "closed-inventory"
  components := [storage]
}

def balance (x : Inventory) : Balance Int inventoryDimension :=
  ⟨x.before, x.after, ⟨0⟩, ⟨0⟩, ⟨0⟩⟩

/-- The interpreter recognizes the complete interface, not only an operation label. -/
def interpretation : Interpretation Inventory where
  component c := if c = storage then some (fun x => (balance x).Holds) else none
  connection _ := none

def model : Model Inventory where
  graph := ⟨design.lower, by decide⟩
  interpretation := interpretation
  supported := by
    constructor
    · intro c hc
      simp [design, Frontend.Design.lower] at hc
      subst c
      exact ⟨fun x => (balance x).Holds, by simp [interpretation]⟩
    · simp [design, Frontend.Design.lower]

def conserved : Contract Inventory :=
  ⟨fun _ => True, fun x => x.after = x.before⟩

theorem inventory_verified : Verified model conserved := by
  constructor
  · refine ⟨⟨⟨4⟩, ⟨4⟩⟩, ?_, trivial⟩
    simp [Model.behavior, Interpretation.Meaning, model, interpretation,
      design, Frontend.Design.lower, balance, Balance.Holds]
  · intro x hx _
    obtain ⟨meaning, found, law⟩ := hx.1 storage (by simp [model, design, Frontend.Design.lower])
    simp [model, interpretation] at found
    subst meaning
    exact Balance.closed_conserves law rfl rfl rfl

/-- An unrecognized operation cannot be assigned an unconstrained meaning. -/
example : ¬interpretation.Meaning
    ⟨"unknown", [⟨"unknown", "unregistered.operation", [], []⟩], []⟩ x := by
  apply unsupported_component (component := ⟨"unknown", "unregistered.operation", [], []⟩)
  · simp
  · decide

/-- Contradictory domain laws must not yield an assurance certificate. -/
def impossible : Model Unit where
  graph := model.graph
  interpretation := ⟨fun _ => some (fun _ => False), fun _ => none⟩
  supported := by
    constructor
    · intro _ _
      exact ⟨_, rfl⟩
    · simp [model, design, Frontend.Design.lower]

example : ¬Verified impossible ⟨fun _ => True, fun _ => True⟩ := by
  intro proof
  obtain ⟨x, hx, _⟩ := proof.feasible
  obtain ⟨meaning, found, law⟩ := hx.1 storage (by simp [impossible, model, design, Frontend.Design.lower])
  cases found
  exact law

/-- A bounded discrete inventory controller; no claim about a continuous plant. -/
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

/-- General pass composition transfers the certificate without reproving the requirement. -/
example (first second : PreservingPass Inventory) :
    Verified ((first.andThen second).run model) conserved :=
  (first.andThen second).verified inventory_verified

end Synthesis.Examples.Assurance
