import Synthesis.Domains.Electronics.Exact.Units
import Synthesis.Domains.Electronics.Exact.Resistor
import Synthesis.Domains.Electronics.Exact.Capacitor
import Synthesis.Domains.Electronics.Exact.Inductor
import Synthesis.Domains.Electronics.Exact.Source

/-! # Exact rational electronics

Umbrella of the exact, computable core of the electronics domain. Coefficients are
rational literals, which is what AST schema 2 stores, so every element re-exported here
can be bound into `IR.Component` parameters without an approximation contract.

The core is deliberately free of Mathlib: it is what the runtime frontend regression
executable links, and keeping it independent preserves the property recorded in
ADR 0004. Continuous time, real-valued coefficients, complex impedance, network topology
and every analytic result live under `Synthesis.Domains.Electronics.Analytic`.

| Module | Content |
| --- | --- |
| `Exact.Units` | parameter and observation types, SI exponent identities |
| `Exact.Resistor` | Ohm's law, Joule dissipation, series/parallel, duality, dividers |
| `Exact.Capacitor` | charge and electrostatic energy, parallel law, elastance |
| `Exact.Inductor` | flux linkage and magnetic energy, series law, reciprocal inductance |
| `Exact.Source` | ideal independent sources and the two single-element solved circuits |
-/
