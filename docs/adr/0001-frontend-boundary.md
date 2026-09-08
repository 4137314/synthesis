# ADR 0001: Lean embedded frontend and proof-carrying graph

Status: accepted

Use a Lean embedded DSL and a small custom graph AST. Keep the implementation free
of external Lean dependencies. Require structural evidence at the consumer boundary.
Use typed dimensional expressions as the foundation for future equation elaboration.

This provides an executable and kernel-checked starting point without committing to
one physics model, solver or target. Physical correctness is a separate predicate
with an explicit proof. Backend implementations are always downstream projects.

The first compiler has a single structural error and identity-style graph lowering.
A textual parser, detailed diagnostics and serialized interchange are deferred until
the semantic contract is sufficiently exercised. Breaking contract changes require
an explicit decision on schema versioning.
