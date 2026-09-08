import Synthesis.Physics.Rational

namespace Synthesis.Domains.Thermal
open Physics
set_option autoImplicit false

/-- Lumped, steady, linear conductance G = k A / L; no geometry or PDE is implied. -/
abbrev Link := Nonnegative Dimension.thermalConductance
abbrev Temperature := Quantity Rat Dimension.temperatureDim
abbrev HeatRate := Quantity Rat Dimension.power

/-- Positive means transfer from the left terminal to the right terminal. -/
def heatRate (link : Link) (left right : Temperature) : HeatRate :=
  ⟨link.quantity.value * (left.value - right.value)⟩

theorem conduction_dimensions :
    Dimension.thermalConductance.mul Dimension.temperatureDim = Dimension.power := by decide

theorem equilibrium (link : Link) (temperature : Temperature) :
    (heatRate link temperature temperature).value = 0 := by
  simp only [heatRate]
  grind

theorem hot_to_cold (link : Link) (left right : Temperature)
    (ordered : right.value ≤ left.value) : 0 ≤ (heatRate link left right).value := by
  apply Rat.mul_nonneg link.nonnegative
  grind

theorem orientation_reversal (link : Link) (left right : Temperature) :
    (heatRate link right left).value = -(heatRate link left right).value := by
  simp only [heatRate]
  grind

/-- A two-terminal ideal link neither creates nor stores power. -/
theorem terminal_conservation (link : Link) (left right : Temperature) :
    (heatRate link left right).value + (heatRate link right left).value = 0 := by
  rw [orientation_reversal]
  grind

/-- This algebraic dissipation inequality is not a full entropy-production theorem. -/
theorem dissipative (link : Link) (left right : Temperature) :
    0 ≤ (heatRate link left right).value * (left.value - right.value) := by
  have h := Rat.mul_nonneg link.nonnegative (square_nonnegative (left.value - right.value))
  simpa [heatRate, Rat.mul_assoc] using h

end Synthesis.Domains.Thermal
