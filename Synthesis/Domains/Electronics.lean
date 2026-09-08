import Synthesis.Physics.Rational

namespace Synthesis.Domains.Electronics
open Physics
set_option autoImplicit false

/-- Ideal constant, passive resistance in coherent SI units. -/
abbrev Resistor := Nonnegative Dimension.resistance
abbrev Current := Quantity Rat Dimension.currentDim
abbrev Voltage := Quantity Rat Dimension.voltage
abbrev Power := Quantity Rat Dimension.power

/-- Passive sign convention: voltage drop follows the reference current direction. -/
def voltage (r : Resistor) (i : Current) : Voltage :=
  ⟨r.quantity.value * i.value⟩

def power (r : Resistor) (i : Current) : Power :=
  ⟨(voltage r i).value * i.value⟩

theorem ohm_dimensions : Dimension.resistance.mul Dimension.currentDim = Dimension.voltage := by decide

theorem power_dimensions : Dimension.voltage.mul Dimension.currentDim = Dimension.power := by decide

theorem joule_law (r : Resistor) (i : Current) :
    (power r i).value = r.quantity.value * (i.value * i.value) := by
  simp [power, voltage, Rat.mul_assoc]

theorem passive (r : Resistor) (i : Current) : 0 ≤ (power r i).value := by
  rw [joule_law]
  exact Rat.mul_nonneg r.nonnegative (square_nonnegative i.value)

/-- Series composition assumes the same current flows through both resistors. -/
def series (a b : Resistor) : Resistor :=
  ⟨⟨a.quantity.value + b.quantity.value⟩, Rat.add_nonneg a.nonnegative b.nonnegative⟩

theorem series_voltage (a b : Resistor) (i : Current) :
    (voltage (series a b) i).value = (voltage a i).value + (voltage b i).value := by
  simp only [voltage, series]
  grind

theorem series_power (a b : Resistor) (i : Current) :
    (power (series a b) i).value = (power a i).value + (power b i).value := by
  simp only [power, voltage, series]
  grind

theorem zero_current (r : Resistor) : (power r ⟨0⟩).value = 0 := by simp [power, voltage]

/-- Existence for every signed rational current, not merely one feasible witness. -/
theorem operating_point_exists (r : Resistor) (i : Current) :
    ∃ v : Voltage, v.value = r.quantity.value * i.value := ⟨voltage r i, rfl⟩

end Synthesis.Domains.Electronics
