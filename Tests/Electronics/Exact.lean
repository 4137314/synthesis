import Synthesis
import Synthesis.Domains
import Synthesis.Bridges

namespace Tests.Electronics
open Synthesis Synthesis.Physics Synthesis.Domains Synthesis.Semantics
set_option autoImplicit false

/-! Regression checks for the exact rational element models and for the AST component
catalog built on them. Positive cases evaluate the models at concrete operating points;
negative cases exercise the rejection paths: excluded parameters, mismatched dimensions,
altered component interfaces and duplicated parameter names. -/

/-! ## Exact rational element models -/

def capacitor : Electronics.Capacitor := ⟨⟨1 / 1000⟩, by norm_num⟩
def inductor : Electronics.Inductor := ⟨⟨2⟩, by norm_num⟩
def conductor : Electronics.Conductor := ⟨⟨1 / 4⟩, by norm_num⟩
def source : Electronics.VoltageSource := ⟨⟨12⟩⟩

example : (Electronics.charge capacitor ⟨10⟩).value = 1 / 100 := by
  norm_num [Electronics.charge, capacitor]

example : (Electronics.capacitiveEnergy capacitor ⟨10⟩).value = 1 / 20 := by
  norm_num [Electronics.capacitiveEnergy, capacitor]

example : (Electronics.inductiveEnergy inductor ⟨3⟩).value = 9 := by
  norm_num [Electronics.inductiveEnergy, inductor]

example : (Electronics.flux inductor ⟨3⟩).value = 6 := by
  norm_num [Electronics.flux, inductor]

example : (Electronics.current conductor ⟨8⟩).value = 2 := by
  norm_num [Electronics.current, conductor]

example : (source.delivered ⟨-1⟩).value = -12 := by
  norm_num [Electronics.VoltageSource.delivered, source]

-- Degenerate storage parameters are excluded by the element types.
example : True := by
  fail_if_success
    have _ : Electronics.Capacitor := ⟨⟨0⟩, by decide⟩
  trivial

example : True := by
  fail_if_success
    have _ : Electronics.Inductor := ⟨⟨-1⟩, by decide⟩
  trivial

example : True := by
  fail_if_success
    have _ : Electronics.Conductor := ⟨⟨-1⟩, by decide⟩
  trivial

-- A capacitance cannot be applied to a current: dimensions are checked by elaboration.
example : True := by
  fail_if_success
    have _ := Electronics.charge capacitor (⟨2⟩ : Quantity Rat Dimension.currentDim)
  trivial

-- Reciprocal parameters exist only for nondegenerate elements.
example : (Electronics.elastance capacitor).quantity.value = 1000 := by
  norm_num [Electronics.elastance, capacitor]

/-! ## Certificates on the compiled component catalog -/

example : (Components.capacitor capacitor).definition.parameters =
    [IR.Standard.rationalParameter "capacitance" .capacitance (1 / 1000)] := rfl

example : Verified (Components.capacitor capacitor).model
    ⟨fun _ => True, fun x => 0 ≤ x.energy.value⟩ :=
  Components.capacitor_energy_nonnegative capacitor

example : Verified (Components.inductor inductor).model
    ⟨fun _ => True, fun x => 0 ≤ x.energy.value⟩ :=
  Components.inductor_energy_nonnegative inductor

example : Verified (Components.conductor conductor).model
    ⟨fun _ => True, fun x => 0 ≤ x.power.value⟩ :=
  Components.conductor_passive conductor

example : Verified (Components.voltageSource source).model
    ⟨fun x => 0 ≤ x.current.value, fun x => 0 ≤ x.delivered.value⟩ :=
  Components.source_delivers source (by decide)

-- Defaults retain exact coefficients, and duplicate declarations are rejected.
example : (Frontend.compile (Components.capacitor capacitor).ir).isOk = true := by decide
example : (Frontend.compile {
    (Components.capacitor capacitor).ir with definitions := [{
      (Components.capacitor capacitor).definition with parameters :=
        [IR.Standard.rationalParameter "capacitance" .capacitance 1,
         IR.Standard.rationalParameter "capacitance" .capacitance 2] }] }).isOk = false := by decide

-- A changed dimension is not the same complete model.
example : (Components.inductor inductor).model.interpretation.meaning
    { (Components.inductor inductor).ir with definitions := [{
      (Components.inductor inductor).definition with parameters :=
        [IR.Standard.rationalParameter "inductance" .capacitance 2] }] } = none := by
  simp [Primitive.model, Primitive.ir, Components.inductor, inductor,
    IR.Module.mk.injEq, IR.Definition.mk.injEq, IR.Standard.rationalParameter,
    IR.Parameter.mk.injEq, IR.Standard.quantity, IR.TypeExpr.mk.injEq,
    IR.Standard.dimensions, Dimension.inductance, Dimension.capacitance]

/-! ## Structural properties of the exact elements -/

-- Stored charge determines the terminal voltage of a nondegenerate capacitor.
example (v w : Electronics.Voltage)
    (equal : (Electronics.charge capacitor v).value = (Electronics.charge capacitor w).value) :
    v.value = w.value := Electronics.charge_injective capacitor v w equal

-- Flux linkage determines the branch current of a nondegenerate inductor.
example (i j : Electronics.Current)
    (equal : (Electronics.flux inductor i).value = (Electronics.flux inductor j).value) :
    i.value = j.value := Electronics.flux_injective inductor i j equal

-- Dissipation is monotone in the resistance at a fixed operating current.
example (i : Electronics.Current) :
    (Electronics.power ⟨⟨2⟩, by decide⟩ i).value ≤ (Electronics.power ⟨⟨5⟩, by decide⟩ i).value :=
  Electronics.power_mono ⟨⟨2⟩, by decide⟩ ⟨⟨5⟩, by decide⟩ i (by norm_num)

-- A source driven backwards absorbs: it has no unconditional passivity theorem.
example : (source.delivered ⟨-3⟩).value = -(source.delivered ⟨3⟩).value :=
  source.delivered_odd ⟨3⟩

-- A dead source exchanges no power, which is the source-killing step of superposition.
example (i : Electronics.Current) : (Electronics.VoltageSource.delivered ⟨⟨0⟩⟩ i).value = 0 :=
  Electronics.VoltageSource.dead_delivers_nothing i

-- The dual solved circuit: an ideal current source across a positive conductance.
example : ∃ v : Electronics.Voltage,
    (⟨⟨2⟩⟩ : Electronics.CurrentSource).drive.value = (1 / 4 : Rat) * v.value ∧
      ∀ w : Electronics.Voltage,
        (⟨⟨2⟩⟩ : Electronics.CurrentSource).drive.value = (1 / 4 : Rat) * w.value →
          w.value = v.value :=
  Electronics.source_node_operating_point ⟨⟨2⟩⟩ ⟨⟨1 / 4⟩, by norm_num⟩

-- Parallel inductors share flux linkage; their reciprocal inductances add.
example (φ : Electronics.Flux) (ia ib : Electronics.Current)
    (fluxA : φ.value = (Electronics.flux inductor ia).value)
    (fluxB : φ.value = (Electronics.flux inductor ib).value) :
    ia.value + ib.value = φ.value *
      ((Electronics.inverseInductance inductor).quantity.value +
        (Electronics.inverseInductance inductor).quantity.value) :=
  Electronics.parallel_inductor_current inductor inductor φ ia ib fluxA fluxB

end Tests.Electronics
