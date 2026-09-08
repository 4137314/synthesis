# ADR 0002: Formal engineering kernel and semantic evidence

Status: accepted; extends ADR 0001. Historical version decisions are superseded by ADR 0003.

The project and package are **synthesis**, with Lean namespace `Synthesis`.
Version 0.2.0 corrects the initial spelling and adds the formal kernel. The graph
schema remains 1: its fields and accepted wiring semantics have not changed.
Namespace imports are a breaking source-API correction, not a serialized migration.

## Decision

Separate reusable foundations from domain theories and from proof-carrying compilation:

- Logic: observation predicates, assume/guarantee contracts, refinement, composition.
- Systems: reachability, inductive invariants and forward simulations.
- Physics: dimension-indexed quantities, equations and integrated balances.
- Semantics: explicit interpretations for every graph component and coupling.
- Frontend: structural compilation and interpretation attachment with coverage evidence.

`Verified` couples a specific semantic model and requirement. It requires a feasible
behavior in the assumption envelope as well as universal conditional satisfaction.
This is stronger than attaching an arbitrary graph predicate to an AST. The earlier
`Frontend.Certified` stays available as low-level graph-predicate evidence and must
not be represented as an engineering assurance certificate.

Semantics-preserving passes prove equality of behavior sets, represented by pointwise
logical equivalence. Composition transfers requirement evidence and feasibility.
Future refinement passes may restrict behaviors, but need a separate feasibility
obligation; subset inclusion alone would permit eliminating every behavior.

## Limits and consequences

These definitions standardize extension interfaces; they do not invent a universal
physics. An interpretation can still be poorly chosen. Domain authors must justify
its relation to physical reality, units, boundary conditions, numerical assumptions,
uncertainty and applicability. Kernel checking proves implications in the supplied
model, not empirical fidelity or regulatory certification.

One feasible behavior is not input receptiveness, deadlock freedom, liveness or
universal realizability. Synchronous shared-observation contract conjunction is not
an automatic feedback compatibility theorem. Forward simulation uses one abstract
step per concrete step; continuous time and stuttering need explicit models.

No target backend, simulator, optimizer or solver is added. Domain-specific semantics
and algorithms grow in dedicated modules/packages that depend on this small kernel.
