import Synthesis.Physics.Rational

namespace Synthesis.Domains.Electronics
open Physics
set_option autoImplicit false

/-! # Exact rational electronics primitives

This module is the exact, computable core of the electronics domain. Coefficients are
rational literals, which is what AST schema 2 stores, so every element defined here can
be bound into `IR.Component` parameters without an approximation contract. Continuous
time, real-valued coefficients, complex impedance and network topology live in the
Mathlib layer under `Synthesis.Domains.Electronics.*`.

All elements are ideal, memoryless at a fixed operating point and use the passive sign
convention: current enters the terminal at the higher reference potential. -/

/-- Ideal constant, passive resistance in coherent SI units. -/
abbrev Resistor := Nonnegative Dimension.resistance

/-- Ideal constant, passive conductance; the dual parameterization of a resistor. -/
abbrev Conductor := Nonnegative Dimension.conductance

/-- Ideal capacitance. Degenerate zero capacitance is excluded so that stored charge
determines terminal voltage. -/
abbrev Capacitor := Positive Dimension.capacitance

/-- Ideal inductance. Degenerate zero inductance is excluded so that flux linkage
determines branch current. -/
abbrev Inductor := Positive Dimension.inductance

abbrev Current := Quantity Rat Dimension.currentDim
abbrev Voltage := Quantity Rat Dimension.voltage
abbrev Power := Quantity Rat Dimension.power
abbrev Charge := Quantity Rat Dimension.charge
abbrev Flux := Quantity Rat Dimension.magneticFlux
abbrev Energy := Quantity Rat Dimension.energy
abbrev Duration := Quantity Rat Dimension.timeDim

/-! ## Dimensional consistency

These are statements about SI exponents only. They are necessary conditions for a
constitutive law, never sufficient evidence that a device obeys it. -/

theorem ohm_dimensions : Dimension.resistance.mul Dimension.currentDim = Dimension.voltage := by decide

theorem power_dimensions : Dimension.voltage.mul Dimension.currentDim = Dimension.power := by decide

theorem conductance_dimensions :
    Dimension.conductance.mul Dimension.voltage = Dimension.currentDim := by decide

theorem capacitance_dimensions :
    Dimension.capacitance.mul Dimension.voltage = Dimension.charge := by decide

theorem inductance_dimensions :
    Dimension.inductance.mul Dimension.currentDim = Dimension.magneticFlux := by decide

theorem energy_dimensions : Dimension.voltage.mul Dimension.charge = Dimension.energy := by decide

theorem resistance_conductance_dual : Dimension.resistance.inv = Dimension.conductance := by decide

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

/-! ## Resistance and conductance duality

Reciprocal parameters exist only for a nondegenerate element: an ideal open circuit has
no finite resistance and an ideal short circuit has no finite conductance. -/

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

/-! ## Ideal independent sources

A source is an idealized boundary condition, not a passive element: it may deliver
energy, so no passivity theorem is available or claimed for it. -/

/-- An ideal voltage source fixes its terminal voltage for every current. -/
structure VoltageSource where
  emf : Voltage

/-- An ideal current source fixes its branch current for every terminal voltage. -/
structure CurrentSource where
  drive : Current

/-- Power delivered by a source into the external circuit, in the active sign convention. -/
def VoltageSource.delivered (s : VoltageSource) (i : Current) : Power := ⟨s.emf.value * i.value⟩

def CurrentSource.delivered (s : CurrentSource) (v : Voltage) : Power := ⟨v.value * s.drive.value⟩

/-- The driving-point equation of a source loaded by one strictly positive resistance,
together with uniqueness of the operating point. This is a genuine solved circuit, not
only a consistency statement. -/
theorem source_loop_operating_point (s : VoltageSource) (r : Positive Dimension.resistance) :
    ∃ i : Current, s.emf.value = r.quantity.value * i.value ∧
      ∀ j : Current, s.emf.value = r.quantity.value * j.value → j.value = i.value := by
  have h := r.positive
  refine ⟨⟨s.emf.value / r.quantity.value⟩, by grind, ?_⟩
  intro j hj
  grind

/-- A loaded ideal source delivers exactly the power the load dissipates. -/
theorem source_power_balance (s : VoltageSource) (r : Resistor) (i : Current)
    (kvl : s.emf.value = (voltage r i).value) :
    (s.delivered i).value = (power r i).value := by
  simp only [VoltageSource.delivered, power]
  rw [kvl]

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

/-! ## Capacitor: charge storage and electrostatic energy -/

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

/-! ## Inductor: flux linkage and magnetic energy -/

/-- Flux linkage of an ideal linear inductor carrying current `i`. -/
def flux (l : Inductor) (i : Current) : Flux := ⟨l.quantity.value * i.value⟩

/-- Magnetic energy `L i² / 2`, a state function of the branch current. -/
def inductiveEnergy (l : Inductor) (i : Current) : Energy :=
  ⟨l.quantity.value * (i.value * i.value) / 2⟩

theorem flux_additive (l : Inductor) (i j : Current) :
    (flux l ⟨i.value + j.value⟩).value = (flux l i).value + (flux l j).value := by
  simp only [flux]
  grind

theorem inductive_energy_nonnegative (l : Inductor) (i : Current) :
    0 ≤ (inductiveEnergy l i).value := by
  have := Rat.mul_nonneg (positive_nonnegative l) (square_nonnegative i.value)
  simp only [inductiveEnergy]
  grind

theorem inductive_energy_even (l : Inductor) (i : Current) :
    (inductiveEnergy l ⟨-i.value⟩).value = (inductiveEnergy l i).value := by
  simp only [inductiveEnergy]
  grind

theorem inductive_energy_flux (l : Inductor) (i : Current) :
    2 * l.quantity.value * (inductiveEnergy l i).value = (flux l i).value * (flux l i).value := by
  simp only [inductiveEnergy, flux]
  grind

/-- Inductances add in series, where both elements carry the same branch current. -/
def seriesInductance (a b : Inductor) : Inductor :=
  ⟨⟨a.quantity.value + b.quantity.value⟩, by
    have ha := a.positive
    have hb := b.positive
    grind⟩

theorem series_flux (a b : Inductor) (i : Current) :
    (flux (seriesInductance a b) i).value = (flux a i).value + (flux b i).value := by
  simp only [flux, seriesInductance]
  grind

theorem series_inductive_energy (a b : Inductor) (i : Current) :
    (inductiveEnergy (seriesInductance a b) i).value =
      (inductiveEnergy a i).value + (inductiveEnergy b i).value := by
  simp only [inductiveEnergy, seriesInductance]
  grind

/-! ## Reciprocal storage parameters

Series capacitance and parallel inductance combine reciprocally. Elastance and
reluctance-like parameters make those laws additive without a division. -/

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

/-- Existence for every signed rational current, not merely one feasible witness. -/
theorem operating_point_exists (r : Resistor) (i : Current) :
    ∃ v : Voltage, v.value = r.quantity.value * i.value := ⟨voltage r i, rfl⟩

end Synthesis.Domains.Electronics
