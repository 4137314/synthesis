import Synthesis.Domains.Electronics.Exact.Resistor
import Synthesis.IR.Standard
import Synthesis.IR.Connector
import Synthesis.Semantics.Connector
import Synthesis.Semantics.Primitive

namespace Synthesis.Domains.Electronics.Interface
set_option autoImplicit false
open Synthesis.IR

def contract (name : String) : ContractId := .named "synthesis.electrical" name
def terminalType : TypeExpr := ⟨contract "terminal", []⟩
def terminal (name : String) : Port :=
  ⟨⟨name⟩, contract "conservative", terminalType, contract "terminal", []⟩

def currentType := Standard.quantity (contract "current") Dimension.currentDim

def resistanceType := Standard.quantity (contract "resistance") Dimension.resistance

def across (name : String) : Term := .apply (contract "potential") [.variable ⟨name⟩]
def through (name : String) : Term := .apply (contract "flow") [.variable ⟨name⟩]

/-- One reusable definition, two acausal terminals, an external coefficient and two
explicit equations. No current/voltage causality is imposed by this representation. -/
def resistorDefinition : Definition where
  id := ⟨["synthesis.electrical", "resistor"]⟩
  parameters := [⟨"R", resistanceType, none⟩]
  ports := [terminal "p", terminal "n"]
  operations := [
    Standard.relation "ohm" (contract "equal") [
      .apply (contract "subtract") [across "p", across "n"],
      .apply (contract "multiply") [.variable "R", through "p"]],
    Standard.relation "terminal-balance" (contract "equal") [
      .apply (contract "add") [through "p", through "n"],
      .literal currentType (.rational 0)]]

structure Point where
  positive : Semantics.Terminal Rat Rat
  negative : Semantics.Terminal Rat Rat

/-- Currents enter the device. The junction convention is the opposite, so an assembly
must negate device currents when constructing junction observations. -/
def Admissible (r : Resistor) (x : Point) : Prop :=
  x.positive.across - x.negative.across = r.quantity.value * x.positive.through ∧
  x.positive.through + x.negative.through = 0

/-- Instantiation binds the reusable definition; parameters are never hidden in its ID. -/
def resistorIR (r : Resistor) : Module := {
  definitions := [resistorDefinition], root := resistorDefinition.id,
  bindings := [⟨"R", .literal resistanceType (.rational r.quantity.value)⟩] }

def resistorModel (r : Resistor) : Semantics.Model Point where
  graph := ⟨resistorIR r, by constructor <;> rfl⟩
  interpretation := ⟨fun m => if m = resistorIR r then some (Admissible r) else none⟩
  supported := ⟨Admissible r, by simp⟩

theorem resistor_meaning (r : Resistor) (x : Point) :
    (resistorModel r).behavior x ↔ Admissible r x := by
  simp [Semantics.Model.behavior, Semantics.Interpretation.Meaning, resistorModel]

/-- The terminal adapter agrees with the established exact Ohm relation. -/
theorem ohm_compatible (r : Resistor) (x : Point) (h : Admissible r x) :
    x.positive.across - x.negative.across = (voltage r ⟨x.positive.through⟩).value := h.1

theorem resistor_verified (r : Resistor) : Semantics.Verified (resistorModel r)
    ⟨fun _ => True, fun x =>
      0 ≤ (x.positive.across - x.negative.across) * x.positive.through⟩ := by
  constructor
  · refine ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, (resistor_meaning r _).mpr ?_, trivial⟩
    simp [Admissible] <;> grind
  · intro x hx _
    change 0 ≤ (x.positive.across - x.negative.across) * x.positive.through
    rw [ohm_compatible r x ((resistor_meaning r x).mp hx)]
    exact passive r ⟨x.positive.through⟩

/-- A homogeneous terminal junction uses the shared conservative predicate; the
mathematical law remains separate from this executable incidence check. -/
def junctionValid (m : Module) (d : Definition) (j : Junction) : Bool :=
  j.contract == contract "conservative" && Connector.conservative (contract "terminal") m d j

end Synthesis.Domains.Electronics.Interface
