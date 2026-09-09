import Synthesis.Domains.Electronics.Exact.Units

namespace Synthesis.Domains.Electronics
open Physics
set_option autoImplicit false

/-! # Exact resistive elements

Ohm's law in both parameterizations, Joule dissipation, the series and parallel algebra
of the two dual coefficients, and the divider identities. Everything is exact rational
arithmetic at a fixed operating point; no temperature coefficient, tolerance, parasitic
or breakdown behaviour is modelled.

Reciprocal parameters exist only for a nondegenerate element: an ideal open circuit has
no finite resistance and an ideal short circuit has no finite conductance. -/

/-! ## Resistor: Ohm's law and Joule dissipation -/

/-- Passive sign convention: voltage drop follows the reference current direction. -/
def voltage (r : Resistor) (i : Current) : Voltage :=
  ⟨r.quantity.value * i.value⟩

def power (r : Resistor) (i : Current) : Power :=
  ⟨(voltage r i).value * i.value⟩

theorem joule_law (r : Resistor) (i : Current) :
    (power r i).value = r.quantity.value * (i.value * i.value) := by
  simp [power, voltage, Rat.mul_assoc]

theorem passive (r : Resistor) (i : Current) : 0 ≤ (power r i).value := by
  rw [joule_law]
  exact Rat.mul_nonneg r.nonnegative (square_nonnegative i.value)

/-- Ohm's law is additive in the current: an ideal resistor is a linear element. -/
theorem voltage_additive (r : Resistor) (i j : Current) :
    (voltage r ⟨i.value + j.value⟩).value = (voltage r i).value + (voltage r j).value := by
  simp only [voltage]
  grind

theorem voltage_homogeneous (r : Resistor) (i : Current) (a : Rat) :
    (voltage r ⟨a * i.value⟩).value = a * (voltage r i).value := by
  simp only [voltage]
  grind

/-- Reversing the reference current reverses the voltage but not the dissipation. -/
theorem voltage_odd (r : Resistor) (i : Current) :
    (voltage r ⟨-i.value⟩).value = -(voltage r i).value := by
  simp only [voltage]
  grind

theorem power_even (r : Resistor) (i : Current) :
    (power r ⟨-i.value⟩).value = (power r i).value := by
  simp only [power, voltage]
  grind

theorem zero_current (r : Resistor) : (power r ⟨0⟩).value = 0 := by simp [power, voltage]

/-- An ideal short circuit carries current at zero terminal voltage. -/
theorem short_circuit (i : Current) : (voltage ⟨⟨0⟩, by decide⟩ i).value = 0 := by
  simp [voltage]

/-- Dissipation vanishes only in the two degenerate cases; there is no lossless
nonzero operating point for a nonzero resistance. -/
theorem power_eq_zero_iff (r : Resistor) (i : Current) :
    (power r i).value = 0 ↔ r.quantity.value = 0 ∨ i.value = 0 := by
  rw [joule_law]
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Rat.mul_eq_zero.mp h |>.elim id id)
  · rintro (h | h) <;> simp [h]

/-- Strictly positive dissipation is the operating regime of a real resistive load. -/
theorem power_positive (r : Resistor) (i : Current)
    (resistive : 0 < r.quantity.value) (flowing : i.value ≠ 0) : 0 < (power r i).value := by
  rw [joule_law]
  exact Rat.mul_pos resistive (square_positive flowing)

/-- Dissipation grows with the resistance at a fixed operating current, which is the
monotonicity a thermal budget relies on. -/
theorem power_mono (a b : Resistor) (i : Current)
    (ordered : a.quantity.value ≤ b.quantity.value) :
    (power a i).value ≤ (power b i).value := by
  rw [joule_law, joule_law]
  exact Rat.mul_le_mul_of_nonneg_right ordered (square_nonnegative i.value)

/-! ## Series and parallel resistive composition -/

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

theorem series_comm (a b : Resistor) : (series a b).quantity.value = (series b a).quantity.value := by
  simp only [series]
  grind

theorem series_assoc (a b c : Resistor) :
    (series (series a b) c).quantity.value = (series a (series b c)).quantity.value := by
  simp only [series]
  grind

theorem series_zero (a : Resistor) :
    (series a ⟨⟨0⟩, by decide⟩).quantity.value = a.quantity.value := by
  simp only [series]
  grind

/-- A series branch is never easier to drive than either of its parts. -/
theorem series_upper_bound (a b : Resistor) :
    a.quantity.value ≤ (series a b).quantity.value := by
  have := b.nonnegative
  simp only [series]
  grind

/-- Kirchhoff's voltage law for a two-element loop driven by a source. -/
theorem loop_voltage_balance (a b : Resistor) (i : Current) (source : Voltage)
    (kvl : source.value = (voltage (series a b) i).value) :
    source.value - (voltage a i).value - (voltage b i).value = 0 := by
  rw [kvl, series_voltage]
  grind

/-! ## Conductance form -/

/-- Ohm's law in conductance form: current is driven by the terminal voltage. -/
def current (g : Conductor) (v : Voltage) : Current :=
  ⟨g.quantity.value * v.value⟩

def conductorPower (g : Conductor) (v : Voltage) : Power :=
  ⟨v.value * (current g v).value⟩

theorem conductor_joule (g : Conductor) (v : Voltage) :
    (conductorPower g v).value = g.quantity.value * (v.value * v.value) := by
  simp only [conductorPower, current]
  grind

theorem conductor_passive (g : Conductor) (v : Voltage) : 0 ≤ (conductorPower g v).value := by
  rw [conductor_joule]
  exact Rat.mul_nonneg g.nonnegative (square_nonnegative v.value)

/-- Parallel composition assumes both elements see the same terminal voltage. -/
def parallel (a b : Conductor) : Conductor :=
  ⟨⟨a.quantity.value + b.quantity.value⟩, Rat.add_nonneg a.nonnegative b.nonnegative⟩

/-- Kirchhoff's current law for two parallel branches at a shared node. -/
theorem parallel_current (a b : Conductor) (v : Voltage) :
    (current (parallel a b) v).value = (current a v).value + (current b v).value := by
  simp only [current, parallel]
  grind

theorem parallel_power (a b : Conductor) (v : Voltage) :
    (conductorPower (parallel a b) v).value =
      (conductorPower a v).value + (conductorPower b v).value := by
  simp only [conductorPower, current, parallel]
  grind

theorem parallel_comm (a b : Conductor) :
    (parallel a b).quantity.value = (parallel b a).quantity.value := by
  simp only [parallel]
  grind

theorem parallel_assoc (a b c : Conductor) :
    (parallel (parallel a b) c).quantity.value = (parallel a (parallel b c)).quantity.value := by
  simp only [parallel]
  grind

/-- An open branch adds no current path. -/
theorem parallel_open (a : Conductor) :
    (parallel a ⟨⟨0⟩, by decide⟩).quantity.value = a.quantity.value := by
  simp only [parallel]
  grind

/-- A parallel node is never harder to drive than either of its branches. -/
theorem parallel_lower_bound (a b : Conductor) :
    a.quantity.value ≤ (parallel a b).quantity.value := by
  have := b.nonnegative
  simp only [parallel]
  grind

/-! ## Resistance and conductance duality -/

/-- The reciprocal conductance of a strictly positive resistance. -/
def reciprocal (r : Positive Dimension.resistance) : Positive Dimension.conductance :=
  ⟨⟨1 / r.quantity.value⟩, reciprocal_positive r.positive⟩

theorem reciprocal_resistance (r : Positive Dimension.resistance) :
    r.quantity.value * (reciprocal r).quantity.value = 1 :=
  Physics.reciprocal_product r.positive

/-- The two parameterizations describe the same element at every operating point. -/
theorem ohm_dual (r : Positive Dimension.resistance) (i : Current) :
    (current ⟨(reciprocal r).quantity, positive_nonnegative (reciprocal r)⟩
      (voltage ⟨r.quantity, positive_nonnegative r⟩ i)).value = i.value := by
  have key := reciprocal_resistance r
  simp only [current, voltage, reciprocal] at key ⊢
  grind

/-- The two parameterizations also agree on dissipation, so no energy statement depends
on the choice between them. -/
theorem dual_power (r : Positive Dimension.resistance) (i : Current) :
    (conductorPower ⟨(reciprocal r).quantity, positive_nonnegative (reciprocal r)⟩
      (voltage ⟨r.quantity, positive_nonnegative r⟩ i)).value =
    (power ⟨r.quantity, positive_nonnegative r⟩ i).value := by
  have dual := ohm_dual r i
  simp only [conductorPower, power] at *
  grind

/-! ## Voltage and current dividers

The divider identities are stated in cleared-denominator form so that they hold without
a nondegeneracy hypothesis; the solved form follows whenever the total is nonzero. -/

/-- Two-resistor voltage divider driven by the shared series current. -/
theorem voltage_divider (a b : Resistor) (i : Current) :
    ((series a b).quantity.value) * (voltage b i).value =
      b.quantity.value * (voltage (series a b) i).value := by
  simp only [voltage, series]
  grind

theorem voltage_divider_solved (a b : Resistor) (i : Current)
    (loaded : (series a b).quantity.value ≠ 0) :
    (voltage b i).value =
      b.quantity.value * (voltage (series a b) i).value / (series a b).quantity.value := by
  have h := voltage_divider a b i
  grind

/-- Two-conductance current divider driven by the shared terminal voltage. -/
theorem current_divider (a b : Conductor) (v : Voltage) :
    ((parallel a b).quantity.value) * (current b v).value =
      b.quantity.value * (current (parallel a b) v).value := by
  simp only [current, parallel]
  grind

/-- Existence for every signed rational current, not merely one feasible witness. -/
theorem operating_point_exists (r : Resistor) (i : Current) :
    ∃ v : Voltage, v.value = r.quantity.value * i.value := ⟨voltage r i, rfl⟩

end Synthesis.Domains.Electronics
