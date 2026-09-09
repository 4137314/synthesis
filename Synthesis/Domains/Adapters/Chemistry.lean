import Synthesis.Domains.Chemistry
import Synthesis.Semantics.Primitive
import Synthesis.IR.Standard

namespace Synthesis.Domains.Components
open Semantics
set_option autoImplicit false

structure ReactionPoint where
  before : List Chemistry.Water.Molecule
  after : List Chemistry.Water.Molecule

def waterFormation : Primitive ReactionPoint where
  definition := {
    id := ⟨["synthesis.models", "water-formation"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.chemistry.water-formation.v1")]
    ports := [⟨"reactants", .named "synthesis.chemistry" "batch", ⟨.named "synthesis.chemistry" "molecular-batch", []⟩, .named "synthesis.relation" "observable", []⟩,
      ⟨"products", .named "synthesis.chemistry" "batch", ⟨.named "synthesis.chemistry" "molecular-batch", []⟩, .named "synthesis.relation" "observable", []⟩]
  }
  meaning x := Chemistry.Water.formation.Step x.before x.after
  valid := by constructor <;> decide

theorem water_atoms_conserved : Verified waterFormation.model ⟨fun _ => True, fun x =>
    ∀ element, Chemistry.inventory (fun species => Chemistry.Water.atoms species element) x.after =
      Chemistry.inventory (fun species => Chemistry.Water.atoms species element) x.before⟩ := by
  apply Primitive.verify
  · refine ⟨⟨Chemistry.Water.formation.reactants, Chemistry.Water.formation.products⟩, ?_, trivial⟩
    exact ⟨[], by simp, by simp⟩
  · intro x hx _ element
    exact Chemistry.Water.formation.conserves _ (Chemistry.Water.formation_balanced element)
      x.before x.after hx

end Synthesis.Domains.Components
