import Synthesis.Physics.Rational

namespace Synthesis.Domains.Electronics
open Physics
set_option autoImplicit false

/-! # Exact electrical parameter and observation types

The vocabulary of the exact rational layer: the four passive parameter types with the
admissibility evidence they carry, the observation types used at a terminal pair, and
the SI exponent identities the constitutive laws must respect.

Coefficients are rational literals, an exact subset of IR schema 3, so every element
built on these types binds into `IR.Parameter` defaults or instance bindings without an approximation
contract. Continuous time, real coefficients, complex impedance and network topology
belong to the Mathlib layer under `Synthesis.Domains.Electronics.Analytic`.

All elements built here are ideal, memoryless at a fixed operating point and use the
passive sign convention: current enters the terminal at the higher reference potential. -/

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

/-- Charge accumulates a current over a duration; the integrated form of `i = dq/dt`
at the level of SI exponents only. -/
theorem charge_dimensions : Dimension.currentDim.mul Dimension.timeDim = Dimension.charge := by decide

/-- Energy accumulates power over a duration. -/
theorem work_dimensions : Dimension.power.mul Dimension.timeDim = Dimension.energy := by decide

/-- Flux linkage accumulates a terminal voltage over a duration, which is Faraday's law
at the level of SI exponents. -/
theorem flux_dimensions : Dimension.voltage.mul Dimension.timeDim = Dimension.magneticFlux := by decide

/-- A time constant carries the dimension of time in both the resistor-capacitor and the
resistor-inductor form. -/
theorem rc_time_dimensions : Dimension.resistance.mul Dimension.capacitance = Dimension.timeDim := by decide

theorem lr_time_dimensions : Dimension.inductance.div Dimension.resistance = Dimension.timeDim := by decide

end Synthesis.Domains.Electronics
