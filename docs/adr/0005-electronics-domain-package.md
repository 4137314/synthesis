# ADR 0005: Layered electronics domain package

Status: accepted. Package/API version 0.4.0; AST schema 2 is unchanged.

## Context

The electronics domain was a single module containing one ideal resistor. Circuit
theory needs interconnection laws, energy storage in continuous time, sinusoidal
steady state and nonlinear devices. Those need different mathematical settings: exact
rational arithmetic for AST coefficients, an arbitrary ordered field for network
algebra, the reals for calculus and the complex numbers for phasors.

## Decision

Split electronics into two layers with an explicit boundary.

`Synthesis.Domains.Electronics` stays exact, rational and free of Mathlib. It holds the
element models whose coefficients are stored as AST schema 2 parameters: resistor,
conductor, capacitor, inductor and the two ideal independent sources, with their
series/parallel algebra, divider identities and energy relations. Reciprocal
parameters (`reciprocal`, `elastance`) exist only for strictly positive coefficients,
so a degenerate element cannot acquire a dual by accident. Keeping this layer Mathlib
free preserves the property recorded in ADR 0004: the runtime frontend test executable
does not link Mathlib.

`Synthesis.Domains.Electronics.*` is the analytic layer and may use Mathlib. Modules are
separated by mathematical setting rather than by device family: `Element` (terminal
relations over an ordered field), `Resistive` (interconnection algebra), `Network`
(Kirchhoff laws and Tellegen's theorem over a finite topology), `Nodal` (the nodal
operator, superposition and solution uniqueness), `Source` (Thévenin/Norton and power
transfer), `Storage` (capacitor and inductor in continuous time), `Transient`
(first-order relaxation), `Phasor` (complex impedance), `Semiconductor` (Shockley diode
and square-law transistor), `Feedback` (negative feedback and operational amplifiers),
`Magnetics` (coupled inductors and ideal transformers), `TwoPort` (impedance and
transmission descriptions) and `Digital` (Boolean identities and static logic levels).

Generic results are stated over `[Field K] [LinearOrder K] [IsStrictOrderedRing K]` so
that a single theorem serves both the exact rational models and the real-valued ones.
Results that need calculus, exponentials or complex numbers are stated over `ℝ` or `ℂ`
and are not generalized.

Sign conventions are explicit and never mixed inside one element: `absorbed` uses the
passive convention, `delivered` the active one, and the Thévenin and Norton forms are
declared active. Ideal sources have no passivity theorem; their certificates carry an
explicit operating-envelope assumption instead.

Four new AST primitives (`conductor`, `capacitor`, `inductor`, `voltageSource`) join
the component catalog, each with a `Semantics.Verified` certificate. The capacitor and
inductor primitives expose a fixed-operating-point interface only: their differential
law belongs to the analytic layer and is not claimed by the AST component.

## Consequences

`scripts/cache.sh` must fetch the enlarged Mathlib import closure; CI depends on it.
Real and complex coefficients still cannot enter the rational AST without an explicit
representation or approximation contract, which remains unwritten. Network theorems
apply to a topology supplied by the caller; the frontend does not yet lower a circuit
graph into that topology, so composing certified primitives into a certified network
remains future work.
