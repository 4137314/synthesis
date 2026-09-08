import Std
import Synthesis.Systems.Transition

namespace Synthesis.Domains.Chemistry
set_option autoImplicit false
universe u v
variable {Species : Type u} {ElementType : Type v}

/-- A finite molecular batch, represented as a list with repeated species. -/
def inventory (weight : Species → Nat) (batch : List Species) : Nat :=
  (batch.map weight).sum

/-- Stoichiometric transformation only; there is no reaction-rate or energy model. -/
structure Reaction (Species : Type u) where
  reactants : List Species
  products : List Species

def Reaction.Balanced (reaction : Reaction Species) (weight : Species → Nat) : Prop :=
  inventory weight reaction.reactants = inventory weight reaction.products

def Reaction.BalancedElements (reaction : Reaction Species)
    (atoms : Species → ElementType → Nat) : Prop :=
  ∀ element, reaction.Balanced (fun species => atoms species element)

/-- Expose a reactant prefix and replace it, keeping the surrounding inventory.
Lists encode finite batches; no claim of complete multiset rewriting is made. -/
def Reaction.Step (reaction : Reaction Species) (before after : List Species) : Prop :=
  ∃ context, before = reaction.reactants ++ context ∧ after = reaction.products ++ context

theorem inventory_append (weight : Species → Nat) (a b : List Species) :
    inventory weight (a ++ b) = inventory weight a + inventory weight b := by
  simp [inventory, List.sum_append]

theorem Reaction.conserves (reaction : Reaction Species) (weight : Species → Nat)
    (balanced : reaction.Balanced weight) (before after : List Species)
    (step : reaction.Step before after) : inventory weight after = inventory weight before := by
  obtain ⟨context, rfl, rfl⟩ := step
  simp only [inventory_append]
  rw [balanced]

/-- Independent batches compose without changing the atom-count criterion. -/
def Reaction.parallel (a b : Reaction Species) : Reaction Species :=
  ⟨a.reactants ++ b.reactants, a.products ++ b.products⟩

theorem Reaction.parallel_balanced (a b : Reaction Species) (weight : Species → Nat)
    (ha : a.Balanced weight) (hb : b.Balanced weight) : (a.parallel b).Balanced weight := by
  simp only [Balanced, parallel, inventory_append]
  rw [ha, hb]

def network (reactions : List (Reaction Species)) (initial : List Species) :
    Systems.TransitionSystem (List Species) where
  initial state := state = initial
  step before after := ∃ reaction ∈ reactions, reaction.Step before after

theorem network_inventory_invariant (reactions : List (Reaction Species))
    (initial : List Species) (weight : Species → Nat)
    (balanced : ∀ reaction ∈ reactions, reaction.Balanced weight) :
    Systems.Invariant (network reactions initial)
      (fun state => inventory weight state = inventory weight initial) := by
  constructor
  · intro state h
    cases h
    rfl
  · intro before after h step
    obtain ⟨reaction, member, step⟩ := step
    exact (reaction.conserves weight (balanced reaction member) before after step).trans h

theorem reachable_elements_conserved (reactions : List (Reaction Species))
    (initial state : List Species) (atoms : Species → ElementType → Nat)
    (balanced : ∀ reaction ∈ reactions, reaction.BalancedElements atoms)
    (reachable : Systems.Reachable (network reactions initial) state) (element : ElementType) :
    inventory (fun species => atoms species element) state =
      inventory (fun species => atoms species element) initial :=
  (network_inventory_invariant reactions initial _
    (fun reaction member => balanced reaction member element)).reachable reachable

namespace Water

inductive Element where
  | hydrogen | oxygen
  deriving DecidableEq, Repr

inductive Molecule where
  | hydrogen | oxygen | water
  deriving DecidableEq, Repr

def atoms : Molecule → Element → Nat
  | .hydrogen, .hydrogen => 2
  | .oxygen, .oxygen => 2
  | .water, .hydrogen => 2
  | .water, .oxygen => 1
  | _, _ => 0

/-- 2 H2 + O2 → 2 H2O. Stoichiometry does not assert spontaneous or safe reaction. -/
def formation : Reaction Molecule := ⟨[.hydrogen, .hydrogen, .oxygen], [.water, .water]⟩

theorem formation_balanced : formation.BalancedElements atoms := by
  intro element
  cases element <;> simp [Reaction.Balanced, formation, inventory, atoms]

end Water
end Synthesis.Domains.Chemistry
