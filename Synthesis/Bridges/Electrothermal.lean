import Synthesis.Domains.Electronics
import Synthesis.Domains.Thermal
import Synthesis.Semantics.Primitive
import Synthesis.IR.Standard

namespace Synthesis.Bridges.Electrothermal
open Domains Physics Semantics
set_option autoImplicit false

/-- Ideal complete conversion of dissipated electrical power into exported heat.
No energy storage, temperature dynamics or unmodeled loss channel is included. -/
def heat (r : Electronics.Resistor) (current : Electronics.Current) : Thermal.HeatRate :=
  Electronics.power r current

theorem power_conserved (r : Electronics.Resistor) (current : Electronics.Current) :
    (heat r current).value = (Electronics.power r current).value := rfl

theorem heat_nonnegative (r : Electronics.Resistor) (current : Electronics.Current) :
    0 ≤ (heat r current).value := Electronics.passive r current

structure Point where
  current : Electronics.Current
  heat : Thermal.HeatRate

def heater (r : Electronics.Resistor) : Primitive Point where
  definition := {
    id := ⟨["synthesis.models", "joule-heater"]⟩
    operations := [IR.Standard.relation "law" (.named "synthesis.models" "synthesis.bridges.joule-heater.v1")]
    ports := [IR.Standard.observable "synthesis.electronics" "current" .currentDim,
      IR.Standard.observable "synthesis.thermal" "heat" .power]
    parameters := [IR.Standard.rationalParameter "resistance" .resistance (r.quantity.value)]
  }
  meaning x := x.heat = heat r x.current
  valid := by constructor <;> simp [IR.Module.identitiesValid, IR.Module.referencesValid,
    IR.Definition.identitiesValid, IR.namesValid, IR.qualifiedValid, IR.unique,
    IR.Module.definition?, IR.Module.acyclic, IR.Standard.rationalParameter,
    IR.Standard.observable, IR.Standard.relation, IR.Operation.name, IR.operationIdentities, IR.Operation.identitiesValid] <;> decide

theorem heater_verified (r : Electronics.Resistor) :
    Verified (heater r).model ⟨fun _ => True, fun x =>
      x.heat.value = (Electronics.power r x.current).value ∧ 0 ≤ x.heat.value⟩ := by
  apply Primitive.verify
  · exact ⟨⟨⟨0⟩, heat r ⟨0⟩⟩, rfl, trivial⟩
  · intro x hx _
    change x.heat.value = (Electronics.power r x.current).value ∧ 0 ≤ x.heat.value
    rw [hx]
    exact ⟨power_conserved r x.current, heat_nonnegative r x.current⟩

end Synthesis.Bridges.Electrothermal
