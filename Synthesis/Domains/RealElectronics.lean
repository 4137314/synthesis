import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Synthesis.Physics.Quantity

namespace Synthesis.Domains.RealElectronics
open Physics
set_option autoImplicit false

/-- The ideal passive resistor over Mathlib's real numbers. This extends the exact
rational catalog without asserting a transient or numerical approximation model. -/
structure Resistor where
  resistance : Quantity ℝ Dimension.resistance
  nonnegative : 0 ≤ resistance.value

abbrev Current := Quantity ℝ Dimension.currentDim
abbrev Voltage := Quantity ℝ Dimension.voltage
abbrev Power := Quantity ℝ Dimension.power

def voltage (r : Resistor) (i : Current) : Voltage := ⟨r.resistance.value * i.value⟩
def power (r : Resistor) (i : Current) : Power := ⟨(voltage r i).value * i.value⟩

theorem joule_law (r : Resistor) (i : Current) :
    (power r i).value = r.resistance.value * i.value ^ 2 := by
  simp only [power, voltage]
  ring

theorem passive (r : Resistor) (i : Current) : 0 ≤ (power r i).value := by
  rw [joule_law]
  exact mul_nonneg r.nonnegative (sq_nonneg i.value)

def series (a b : Resistor) : Resistor :=
  ⟨⟨a.resistance.value + b.resistance.value⟩, add_nonneg a.nonnegative b.nonnegative⟩

theorem series_power (a b : Resistor) (i : Current) :
    (power (series a b) i).value = (power a i).value + (power b i).value := by
  simp only [power, voltage, series]
  ring

/-- Real coefficients are mathematical parameters. The current rational AST does not
silently round or serialize them. -/
theorem operating_point_exists (r : Resistor) (i : Current) :
    ∃ v : Voltage, v.value = r.resistance.value * i.value := ⟨voltage r i, rfl⟩

end Synthesis.Domains.RealElectronics
