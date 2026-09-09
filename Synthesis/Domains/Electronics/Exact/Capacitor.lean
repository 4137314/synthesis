import Synthesis.Domains.Electronics.Exact.Units

namespace Synthesis.Domains.Electronics
open Physics
set_option autoImplicit false

/-! # Exact capacitive storage

The charge and energy state functions of an ideal linear capacitor at a fixed terminal
voltage, the parallel combination law, and the elastance parameterization that makes
the series law additive without a division.

This is the algebraic face of the element. Its differential law `i = dq/dt` needs
continuous time and lives in `Synthesis.Domains.Electronics.Storage`. Dielectric loss,
leakage, voltage coefficient, ageing and temperature dependence are not modelled. -/

/-- Stored charge of an ideal linear capacitor at terminal voltage `v`. -/
def charge (c : Capacitor) (v : Voltage) : Charge := ⟨c.quantity.value * v.value⟩

/-- Electrostatic energy `C v² / 2`. It is a state function of the terminal voltage. -/
def capacitiveEnergy (c : Capacitor) (v : Voltage) : Energy :=
  ⟨c.quantity.value * (v.value * v.value) / 2⟩

theorem charge_additive (c : Capacitor) (v w : Voltage) :
    (charge c ⟨v.value + w.value⟩).value = (charge c v).value + (charge c w).value := by
  simp only [charge]
  grind

theorem charge_zero (c : Capacitor) : (charge c ⟨0⟩).value = 0 := by simp [charge]

/-- Stored charge determines the terminal voltage: this is why zero capacitance is
excluded from the parameter type. -/
theorem charge_injective (c : Capacitor) (v w : Voltage)
    (equal : (charge c v).value = (charge c w).value) : v.value = w.value := by
  have nonzero : c.quantity.value ≠ 0 := by have := c.positive; grind
  simp only [charge] at equal
  have factored : c.quantity.value * (v.value - w.value) = 0 := by grind
  rcases Rat.mul_eq_zero.mp factored with degenerate | difference
  · exact absurd degenerate nonzero
  · grind

theorem capacitive_energy_nonnegative (c : Capacitor) (v : Voltage) :
    0 ≤ (capacitiveEnergy c v).value := by
  have := Rat.mul_nonneg (positive_nonnegative c) (square_nonnegative v.value)
  simp only [capacitiveEnergy]
  grind

/-- Stored energy does not depend on the polarity of the terminal voltage. -/
theorem capacitive_energy_even (c : Capacitor) (v : Voltage) :
    (capacitiveEnergy c ⟨-v.value⟩).value = (capacitiveEnergy c v).value := by
  simp only [capacitiveEnergy]
  grind

/-- The charge form of the stored energy, cleared of its denominator: `2 C E = q²`. -/
theorem capacitive_energy_charge (c : Capacitor) (v : Voltage) :
    2 * c.quantity.value * (capacitiveEnergy c v).value = (charge c v).value * (charge c v).value := by
  simp only [capacitiveEnergy, charge]
  grind

theorem capacitive_energy_zero_iff (c : Capacitor) (v : Voltage) :
    (capacitiveEnergy c v).value = 0 ↔ v.value = 0 := by
  have h := c.positive
  simp only [capacitiveEnergy]
  constructor
  · intro hzero
    grind
  · intro hzero
    grind

/-- Capacitances add in parallel, where both elements share the terminal voltage. -/
def parallelCapacitance (a b : Capacitor) : Capacitor :=
  ⟨⟨a.quantity.value + b.quantity.value⟩, by
    have ha := a.positive
    have hb := b.positive
    grind⟩

theorem parallel_charge (a b : Capacitor) (v : Voltage) :
    (charge (parallelCapacitance a b) v).value = (charge a v).value + (charge b v).value := by
  simp only [charge, parallelCapacitance]
  grind

theorem parallel_capacitive_energy (a b : Capacitor) (v : Voltage) :
    (capacitiveEnergy (parallelCapacitance a b) v).value =
      (capacitiveEnergy a v).value + (capacitiveEnergy b v).value := by
  simp only [capacitiveEnergy, parallelCapacitance]
  grind

theorem parallel_capacitance_comm (a b : Capacitor) :
    (parallelCapacitance a b).quantity.value = (parallelCapacitance b a).quantity.value := by
  simp only [parallelCapacitance]
  grind

theorem parallel_capacitance_assoc (a b c : Capacitor) :
    (parallelCapacitance (parallelCapacitance a b) c).quantity.value =
      (parallelCapacitance a (parallelCapacitance b c)).quantity.value := by
  simp only [parallelCapacitance]
  grind

/-! ## Reciprocal storage parameters

Series capacitors combine reciprocally. Elastance makes that law additive without a
division, in the same way conductance does for parallel resistors. -/

/-- Elastance, the reciprocal of capacitance. -/
def elastance (c : Capacitor) : Positive (Dimension.capacitance.inv) :=
  ⟨⟨1 / c.quantity.value⟩, reciprocal_positive c.positive⟩

theorem elastance_capacitance (c : Capacitor) :
    c.quantity.value * (elastance c).quantity.value = 1 :=
  Physics.reciprocal_product c.positive

/-- Series capacitors carry a common charge; their elastances add. This is the
division-free statement of the reciprocal series-capacitance law. -/
theorem series_capacitor_voltage (a b : Capacitor) (q : Charge) (va vb : Voltage)
    (chargeA : q.value = (charge a va).value) (chargeB : q.value = (charge b vb).value) :
    va.value + vb.value = q.value * ((elastance a).quantity.value + (elastance b).quantity.value) := by
  have ha := elastance_capacitance a
  have hb := elastance_capacitance b
  simp only [charge] at chargeA chargeB
  grind

/-- Series capacitors also add their stored energies, because each stores `q² S / 2`
with the same common charge. -/
theorem series_capacitor_energy (a b : Capacitor) (q : Charge) (va vb : Voltage)
    (chargeA : q.value = (charge a va).value) (chargeB : q.value = (charge b vb).value) :
    (capacitiveEnergy a va).value + (capacitiveEnergy b vb).value =
      q.value * (va.value + vb.value) / 2 := by
  simp only [capacitiveEnergy]
  simp only [charge] at chargeA chargeB
  grind

end Synthesis.Domains.Electronics
