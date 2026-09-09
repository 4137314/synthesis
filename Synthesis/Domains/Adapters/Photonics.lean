import Synthesis.Domains.Photonics
import Synthesis.Semantics.Primitive
import Synthesis.IR.Standard

namespace Synthesis.Domains.Components
open Physics Semantics
set_option autoImplicit false

structure OpticalPoint where
  input : Photonics.OpticalPower
  transmitted : Quantity Rat Dimension.power
  reflected : Quantity Rat Dimension.power
  absorbed : Quantity Rat Dimension.power

def splitter (s : Photonics.Splitter) : Primitive OpticalPoint where
  definition := {
    id := ⟨["synthesis.models", "splitter"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.photonics.power-splitter.v1")]
    ports := [IR.Standard.observable "synthesis.photonics" "input" .power,
      IR.Standard.observable "synthesis.photonics" "transmitted" .power,
      IR.Standard.observable "synthesis.photonics" "reflected" .power,
      IR.Standard.observable "synthesis.photonics" "absorbed" .power]
    parameters := [IR.Standard.rationalParameter "transmittance" .scalar (s.transmittedFraction),
      IR.Standard.rationalParameter "reflectance" .scalar (s.reflectedFraction)]
  }
  meaning x := x.transmitted = Photonics.transmitted s x.input ∧
    x.reflected = Photonics.reflected s x.input ∧ x.absorbed = Photonics.absorbed s x.input
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem optical_conservation (s : Photonics.Splitter) :
    Verified (splitter s).model ⟨fun _ => True, fun x =>
      x.transmitted.value + x.reflected.value + x.absorbed.value = x.input.quantity.value⟩ := by
  apply Primitive.verify
  · let input : Photonics.OpticalPower := ⟨⟨0⟩, Rat.le_refl⟩
    exact ⟨⟨input, Photonics.transmitted s input, Photonics.reflected s input, Photonics.absorbed s input⟩,
      ⟨rfl, rfl, rfl⟩, trivial⟩
  · intro x hx _
    change x.transmitted.value + x.reflected.value + x.absorbed.value = x.input.quantity.value
    rw [hx.1, hx.2.1, hx.2.2]
    exact Photonics.power_conservation s x.input

end Synthesis.Domains.Components
