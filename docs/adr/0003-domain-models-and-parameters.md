# ADR 0003: Exact domain models and parameterized AST

Status: accepted. Package/API version 0.3.0; AST schema 2.

## Decision

Introduce separate domain and bridge umbrellas, leaving `Synthesis` as the reusable
kernel. Initial domains use exact rational scalars, finite batches or complex rational
amplitudes. This supports useful algebraic and invariant proofs without adding a large
external dependency. Irrational/continuous models require a future explicit extension.

`Core.Parameter` records a name, SI dimension and rational literal. `IR.Component`
now has a parameter list. The structural validator rejects empty or duplicate parameter
names. Domain admissibility is checked by proof-carrying parameter types and exact
component recognition, not by generic structural validation.

`Semantics.Primitive` binds a complete parameterized component to a relation, proves
its structural validity and exposes a non-vacuous verification interface. Recognizers
compare the complete component; modifying a coefficient or interface cannot silently
reuse an incompatible interpretation. Cross-domain conversion belongs in a bridge.

## Migration

Schema 1 components become schema 2 components with `parameters := []`. Existing
positional constructors need the fourth field; record constructors may use the default.
Downstream consumers must explicitly support schema 2 and reject unsupported parameters.
There is still no serialized interchange, so this is an in-memory/API migration.

## Proof policy

Physical laws are model definitions or explicit hypotheses, not added global logical
assumptions. Each domain documents its applicability, proves its advertised properties,
and includes negative regressions. The audit imports every project module and rejects
unapproved transitive proof assumptions. Standard Lean foundational assumptions remain
permitted. No claim of proving empirical physics or industrial certification is made.
