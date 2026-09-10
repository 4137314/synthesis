# Frontend infrastructure

The existing `engineering` and `engineering_system` syntax remains an embedded Lean
frontend. Domain syntax extends Lean's parser and elaborates ordinary checked terms.
This is not a standalone engineering parser or an automatic domain-law solver.

`DesignBuilder.declare` runs a definition declaration program. `addDefinition` rejects
an existing identity immediately; `finish` checks the entire module and returns
Validated or diagnostics, never a partially mutated module. DefinitionHandle is a
logical declaration handle, not proof of resolution after arbitrary edits.

`resolveReference` resolves an EntityRef against a module and checks a caller-supplied
entity-kind predicate. Reference carries both proofs and is indexed by the exact
module snapshot. Private frontends can choose their own predicates and expected kinds.
IR.Extension.infer continues to own term typing and value-dependent signatures.

`sourced_operation` attaches the source file and syntax byte span to an operation,
retaining other provenance fields. `SourceDocument.range` maps portable offsets to
zero-based lines and UTF-8 byte columns. `SourceMap` can attach spans to any fine-grained
entity, including entities without a provenance field in schema 3. Module.atSource
queries provenance already embedded in canonical declarations. Missing positions are
not inferred. Editors that require UTF-16 columns must explicitly convert them.

The implementation does not capture every declaration span automatically, resolve
arbitrary domain-specific names, or recover from every elaboration error. Domain DSLs
reuse these helpers and Lean's expected-type elaboration; their syntax and diagnostics
remain domain-owned. The public query layer contains introspection logic, so terminal,
IDE and AI tooling need not parse command output or inspect private containers.


API 0.6.1 adds ElaborationContext with explicit module/definition/instance scope,
innermost-first name bindings, parameter typing context, expected type, active
ExtensionSet and source/generation metadata. resolveName distinguishes unresolved and
ambiguous names; infer reports expected/actual type mismatch. Definition construction
checks member identities before committing a definition to builder state.

RevisionSourceMap wraps a local SourceMap with immutable revision context.
sourceOfEntity rejects stale revision references; entityAtPosition returns LocatedEntity.
GeneratedOrigin records located parents and the generating frontend construct. Domain
elaborators supply these explicit relationships; they are not guessed from text names.
