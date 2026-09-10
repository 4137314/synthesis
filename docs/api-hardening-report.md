# Historical API 0.6.0 hardening report

This records the b4a0882 baseline. ADR 0009 and the stability report supersede its
linear-index, derived-codec and local-only-trace descriptions.

## Changes and compatibility

1. **Files.** New public modules: Core.Version; IR.Entity, Query, Index, Composition,
   Render, Serialization; Design.Adapter, Realization; Frontend.Scope, Source,
   Construction; Interop.Validation. Umbrellas, inspectors, diagnostics, traces, test
   roots, documentation checks and repository checks are migrated. Existing domain
   mathematics and model definitions are retained.
2. **Versions.** API 0.6.0; logical IR schema 3 unchanged; reference serialization format
   1; generic interop protocol 1. No dependency pins or target backends are added.
3. **Public boundary.** Logical queries and snapshot-bound reference evidence are the
   preferred consumer interface. Canonical constructors remain available to low-level
   importers. The stability policy separates supported concepts from experimental
   syntax and implementation fields. No artificial Internal module hierarchy was
   added just to move files; private traversal/index helpers are private declarations.
4. **Breaking changes.** Trace.source/target now contain EntityRef rather than
   QualifiedId. Wrap old definition IDs as `{ definition := some id }`. Diagnostic
   now supports fine-grained subjects, related entities and notes. No permanent
   compatibility aliases or parallel schema were introduced.

## Infrastructure

5. **Identity.** EntityRef selects a reusable definition, instance occurrence path and
   local declaration steps. Named parameters, ports, instances, junctions, operations,
   results and bindings survive unrelated reorderings. Arguments and repeated
   attributes are explicitly positional. Module.resolve returns resolution evidence
   for the exact snapshot. Requirement operations use the same locator system.
6. **Queries/index.** Deterministic definition-table preorder, hierarchy expansion with
   depth exhaustion diagnostics, contract/kind filtering, source-position queries,
   definition-reference queries and folds. Index is a private array snapshot;
   Index.findDefinition_eq proves agreement with canonical lookup. It is deliberately
   not advertised as an efficient hash/tree index.
7. **Extensions.** ExtensionPackage manifests assign exclusive contract ownership.
   combineMany rejects duplicates with structured contract/package information.
   Handler rejection cannot fall through to another owner. AttributeCodec and
   TypeFamily have exact decode/encode theorems; OperationSchema and InterfaceSchema
   supply typed domain construction helpers.
8. **Serialization.** Deterministic compact JSON with independent envelope versions,
   normalized exact rationals, all canonical fields and open payloads retained.
   Decoder rejects unknown/omitted fields, unsupported versions, malformed input and
   configured byte/nesting-limit violations. Codec.Exact distinguishes a proved
   codec law from runtime conformance; the JSON implementation has tests, not a
   general round-trip theorem. Round trips apply within supported schema and budgets.
9. **Migration.** Migration wraps a typed Stage with explicit schema boundaries;
   composition rejects incompatible intermediate versions. Stage disclosures and
   Establishes proofs remain available. No fictitious schema 4 or implicit upgrade.
10. **Diagnostics.** Structured subjects, related entities, notes, expected/actual data,
    remediation and source offsets. Stable new SYN codes cover resolution, ownership,
    decoding, versions, budgets, frontend duplicates and prerequisite rejection.
    Existing E codes remain for established structural/extension checks.
11. **Evidence.** EvidenceReport is an open-method report with dependencies and subjects.
    ProofEvidence contains an actual proof. CertifiedTranslation requires a proof of
    a caller-selected relation. No conversion from an external report into proof is
    provided. The existing feasibility-sensitive Semantics.Verified remains intact.
12. **Interop.** Requirement conjunction accumulates both failures; Stage.requiring
    guards any representation-changing stage. Composition retains diagnostics,
    obligations, assumptions, erasures and trace edges. Trace.compose joins an
    end-to-end view through an explicitly shared intermediate revision.
    Equivalent.trans is kernel proved. BackendProfile is descriptive only and Backend
    ties it to the actual Exporter target. Sufficiency still gates artifact production.
13. **Frontend.** Transactional DesignBuilder rejects duplicate definitions and returns
    Validated only after whole-module checks. Generic typed Reference carries a
    caller-selected entity-kind predicate. sourced_operation captures syntax origin;
    SourceDocument and SourceMap support editor coordinates and fine-grained sources.
    Inspect commands now consume shared folds instead of definition storage directly.
14. **Realization.** Specification, TechnologyContext, RealizationProblem, Realization
    and CertifiedRealization separate requirements, admissible implementation space,
    candidates, feasibility and satisfaction. ParameterSpace permits open role IDs
    and arbitrary admissibility sets. No solver or concrete-parameter guessing.

## Conformance and limits

15. **Consumer impact.** Existing domains build unchanged. External packages can import
    only Synthesis; the repository checker enforces this for Tests.ExternalPackage.
    The stable surface is semantic/source-level, not a C ABI or a frozen list layout.
16. **Tests.** Tests.PublicAPI covers generated recursive JSON round trips, a deterministic
    format-1 golden, locator/result agreement, malformed/unknown/version/size/depth
    rejection, trace joins, source maps/capture, extension conflicts, migrations,
    translation validation and certified realization. Tests.ExternalPackage defines
    a private hydraulic type/interface/operation, symbolic hierarchy, multiway
    junction, composed extension, query, stage and rejecting exporter using public
    imports. Tests.Targets adds systems allocation/hierarchy and logical-to-layout
    fine-grained trace checks to existing digital/continuous/layout/FEM fixtures.
17. **Risks and deliberately unclaimed guarantees.** The index is currently linear;
    no million-entity benchmark or asymptotic scalability claim. Frontend syntax is
    extensible but does not automatically resolve every private domain's names or
    capture every declaration span. Positional references require explicit remapping.
    Trace joins require callers to supply the same intermediate module revision.
    JSON codecs are runtime-tested and Lean-version-pinned, not theorem-proved.
    Canonical decoding does not establish structural validity, semantics, physical
    applicability or artifact correctness. No backend, solver, automatic specialization,
    certified geometry generator or full industrial denial-of-service guarantee exists.
18. **Verification.** `nix develop --command bash scripts/check.sh` executes repository
    closure/layer checks, `lake build`, `lake test` and `lake env lean Tests/Audit.lean`.
    Final run passed: 122 modules in audit closure, 2867 build jobs and runtime tests.
    `nix develop --command nixfmt --check flake.nix`, `nix flake check` and
    `git diff --check` passed. The flake check covered the host system; Nix reported
    incompatible systems as omitted. Documentation generation is checked separately
    using `nix develop --command bash scripts/docs.sh`; the final run passed with
    106 generated project modules and 107 public API pages/search data verified. An
    earlier run overlapped a Lean rebuild and failed on an unavailable object file;
    it was rerun successfully after the completed build.

No kernel trust shortcuts were introduced. Only the established foundational axioms
are permitted by the transitive audit. Tests and external reports are not promoted to
engineering certificates.
