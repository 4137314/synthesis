# ADR 0006: Electronics module decomposition and dynamic layer

Status: accepted. Package/API version 0.4.0; AST schema 2 is unchanged.

## Context

ADR 0005 split electronics into an exact rational core and a Mathlib analytic layer.
That split solved the mathematical-setting problem but left two structural ones.

First, several modules had grown past the point where their contents could be located
by name. The exact core was a single 439-line module holding five unrelated element
families; `Element`, `TwoPort`, `Storage`, `Magnetics`, `Digital`, `Semiconductor` and
`Phasor` each carried two or three independent theories with different hypotheses. A
consumer wanting only the resistor could not import only the resistor, and the doc-gen
pages listed unrelated theorems under one heading.

Second, the dynamic layer stopped at first order. Uniqueness of the first-order solution
was proved inline in `Transient`, so nothing else could reuse it, and there was no model
of a circuit with two storage elements at all — which is where the engineering content
of transient analysis begins.

## Decision

**Decompose by theory, not by file size.** Every module that held more than one theory is
now a directory with one module per theory plus an umbrella that re-exports them and
carries the map. The umbrella keeps the module name that consumers already import, so no
external import breaks.

- `Electronics` (exact core) → `Electronics.Exact.{Units, Resistor, Capacitor, Inductor,
  Source}`.
- `Element` → `Element.{Basic, Interconnect, Passivity}`.
- `Storage` → `Storage.{Capacitor, Inductor}`.
- `Magnetics` → `Magnetics.{Coupled, Transformer}`.
- `Semiconductor` → `Semiconductor.{Diode, Mosfet}`.
- `Digital` → `Digital.{Gate, Level, Cmos}`.
- `Phasor` → `Phasor.{Impedance, Resonance}`.
- `TwoPort` → `TwoPort.{Impedance, Admittance, Transmission, Conversion}`.

A new umbrella `Electronics.Analytic` collects the whole Mathlib layer, so
`Synthesis.Domains` names two electronics modules instead of thirteen. The exact core
umbrella `Synthesis.Domains.Electronics` remains Mathlib free, which preserves the
property recorded in ADR 0004: the runtime frontend regression executable does not link
Mathlib.

**Factor the shared mathematics out of the circuit modules.** `Electronics.Ode` holds the
scalar linear differential equation `x' = a x`, its exponential solution and its
uniqueness. `Transient` now instantiates it rather than reproving it, and `SecondOrder`
uses it twice, once for each factor of the characteristic polynomial.

**Parameterize the second-order model by its ODE coefficients**, not by the damping ratio
and the natural frequency. `SecondOrder.Damped` carries `dissipation` and `stiffness`, so
the constructors in `Rlc` are division free and no square root enters the circuit
derivation. `dampingRatio` and `naturalFrequency` are derived quantities with their own
lemmas, and the regime classification is decided by the sign of the discriminant.

**Derive circuit equations rather than postulate them.** `Rlc.series_loop_solves` and
`Rlc.parallel_node_solves` take Kirchhoff's law as an identity in time plus the element
constitutive law, differentiate the identity, and eliminate the remaining state variable.
The second-order equation is a conclusion, not a hypothesis.

**Add the missing one-port theorem.** `Electronics.Thevenin` models an affine one-port
`v = e + r i`, proves that the family is closed under series and parallel
interconnection, and proves that the equivalent is *unique*. Uniqueness is the step that
licenses identifying a source by measuring its open-circuit voltage and terminal slope,
and it was previously absent.

**Complete the frequency-domain layer.** `Electronics.Power` gives the product-to-sum
decomposition of instantaneous power and the complex power triangle; `Electronics.Filter`
gives the first-order responses with the half-power cutoff stated exactly as
`normSq = 1/2`, with no decibel approximation and no logarithm. `TwoPort.Admittance` and
`TwoPort.Conversion` add the dual description and the partial changes of coordinates,
each carrying its nondegeneracy hypothesis explicitly.

## Consequences

Import granularity is now per theory: a consumer that needs only Kirchhoff's laws does not
compile the diode model. Umbrella modules are documentation as well as re-exports; each
carries a table of what its parts contain.

`scripts/cache.sh` gains `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv` for the
underdamped response. The electronics regression tests are split along the same four
boundaries as the package (`Tests.Electronics.{Exact, Network, Dynamics, Devices}`).

The averaging step of "average power" is still not proved: `Power` decomposes the
instantaneous product exactly, but integrating the double-frequency term over a period is
future work. Underdamped uniqueness is likewise open — only the overdamped regime has a
completeness theorem for its modes. Thévenin closure covers series and parallel assembly
only; a bridge topology is not reachable by those two operations, so the general network
form of the theorem remains unproved.
