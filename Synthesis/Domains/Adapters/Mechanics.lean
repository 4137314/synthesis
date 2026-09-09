import Synthesis.Domains.Mechanics
import Synthesis.Semantics.Primitive
import Synthesis.IR.Standard

namespace Synthesis.Domains.Components
open Physics Semantics
set_option autoImplicit false

structure ElasticPoint where
  strain : Mechanics.Strain
  stress : Mechanics.Stress
  energyDensity : Quantity Rat Dimension.pressure

def elasticMaterial (material : Mechanics.ElasticMaterial) : Primitive ElasticPoint where
  definition := {
    id := ⟨["synthesis.models", "elastic-material"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.mechanics.linear-elastic.v1")]
    ports := [IR.Standard.observable "synthesis.mechanics" "strain" .scalar,
      IR.Standard.observable "synthesis.mechanics" "stress" .pressure,
      IR.Standard.observable "synthesis.mechanics" "energy-density" .pressure]
    parameters := [IR.Standard.rationalParameter "young-modulus" .pressure (material.quantity.value)]
  }
  meaning x := x.stress = Mechanics.stress material x.strain ∧
    x.energyDensity = Mechanics.energyDensity material x.strain
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem elastic_passive (material : Mechanics.ElasticMaterial) :
    Verified (elasticMaterial material).model ⟨fun _ => True, fun x => 0 ≤ x.energyDensity.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, Mechanics.stress material ⟨0⟩, Mechanics.energyDensity material ⟨0⟩⟩,
      ⟨rfl, rfl⟩, trivial⟩
  · intro x hx _
    change 0 ≤ x.energyDensity.value
    rw [hx.2]
    exact Mechanics.energy_nonnegative material x.strain

end Synthesis.Domains.Components
