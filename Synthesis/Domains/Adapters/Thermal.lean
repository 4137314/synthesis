import Synthesis.Domains.Thermal
import Synthesis.Semantics.Primitive
import Synthesis.IR.Standard

namespace Synthesis.Domains.Components
open Physics Semantics
set_option autoImplicit false

structure ThermalPoint where
  left : Thermal.Temperature
  right : Thermal.Temperature
  heatRate : Thermal.HeatRate

def thermalLink (g : Thermal.Link) : Primitive ThermalPoint where
  definition := {
    id := ⟨["synthesis.models", "thermal-link"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.thermal.conductance.v1")]
    ports := [IR.Standard.observable "synthesis.thermal" "left" .temperatureDim,
      IR.Standard.observable "synthesis.thermal" "right" .temperatureDim,
      IR.Standard.observable "synthesis.thermal" "heat-rate" .power]
    parameters := [IR.Standard.rationalParameter "conductance" .thermalConductance (g.quantity.value)]
  }
  meaning x := x.heatRate = Thermal.heatRate g x.left x.right
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem thermal_direction (g : Thermal.Link) :
    Verified (thermalLink g).model
      ⟨fun x => x.right.value ≤ x.left.value, fun x => 0 ≤ x.heatRate.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, ⟨0⟩, Thermal.heatRate g ⟨0⟩ ⟨0⟩⟩, rfl, Rat.le_refl⟩
  · intro x hx ha
    change 0 ≤ x.heatRate.value
    rw [hx]
    exact Thermal.hot_to_cold g x.left x.right ha

end Synthesis.Domains.Components
