# API 0.6.1 stabilization report

## Baseline and version decision

Audited base: `b4a08820801b3aa6c8a9fd75ab69c6700f9e1e07`.
The baseline already supplied the open-world schema, rich semantic model, extensions,
requirements, realization and translation validation APIs. This pass strengthens their
surrounding infrastructure; it does not replace the engineering AST or add target backends.

| Boundary | Result |
| --- | --- |
| Lean source API | 0.6.1 |
| Canonical IR schema | 3, unchanged |
| Module wire format | 1, existing canonical fixture retained |
| Interop protocol | 2, revision-qualified traces and reports |
| Fingerprint scheme | `synthesis.fingerprint / fnv1a64-be`, version 1 |

## Implemented public surface and files

- `Core/Revision`: logical revision identity plus optional versioned content digest.
  FNV-1a-64 fingerprints canonical bytes; it is explicitly noncryptographic.
- `IR/Revision`: `ModuleRevision.create` caches a module fingerprint with a Lean
  correspondence proof. `LocatedEntity` qualifies a local locator; snapshot resolution
  rejects another revision. Manual protocol codecs and deterministic renderers are public.
- `Interop/Transform`: traces carry both revision boundaries. Checked composition rejects
  different intermediate revisions even when local entity paths are identical. Stage
  disclosures also check boundaries when traces are empty. Composition retains original
  edges in history and produces an end-to-end trace view.
- `IR/Serialization`: explicit field/tag encoders and decoders replace derived public
  layouts. Exact rationals, nested open data, operations and every schema-3 field survive.
  Duplicate JSON keys, including escaped aliases, are rejected before parser coalescing.
  Byte/nesting budgets and recursive decoder bounds prevent unchecked descent.
- `IR/Index`: a private derived hash map replaces linear definition lookup. Lean theorems
  establish agreement for definition lookup, hierarchical descent and entity resolution,
  including the canonical first-occurrence rule for malformed duplicate definitions.
- `IR/Query`: public traversal order is unchanged. Definition traversal accumulates chunks;
  hierarchy traversal shares a definition table. Neither depends on hash iteration order.
- `IR/Composition`: `ExtensionSet` exposes active contracts and package ownership from
  explicit composition. Rejection by an owning handler never falls through to a rival.
- `Frontend/Context`, `Frontend/Provenance`, `Frontend/Construction`: explicit scopes,
  expected-type inference, checked aliases, generated lineage and revision-qualified source
  maps; local definition identity is checked before builder commit. Definition navigation
  resolves the actual hierarchical scope. Existing typed references remain snapshot-bound.
- `Interop/Validation`: explicit evidence outcome, claim, tool, input/output revisions,
  certificate reference and located subjects. `TracedTranslation` carries a revision-safety
  proof; `RoundTripEncoder` separates encoding correctness from semantic lowering and has
  an injectivity theorem. Requirements/checkers support contramapping.
- `Interop/Protocol`: explicit protocol-2 trace and evidence report encoding/decoding.
  Deserialized reports never become `ProofEvidence`.

`Specification`, `TechnologyContext`, `RealizationProblem`, `CertifiedRealization`,
`Validated`, `Checked`, `Semantics.Verified`, `Refines` and `Equivalent` retain their
established meanings. Generation remains separate from certification. Refinement means
that each concrete behavior projects to an admissible abstract behavior; feasibility is
separate. Preservation metadata is not a proof.

## Migration and compatibility

Schema migrations retain typed source/target stages. `Migration.andThen` checks schema
boundaries, and execution inherits revision checking from `Stage.andThen`. Tests use
small test-only schemas; no invented production schema or automatic reinterpretation
is introduced.

For source consumers upgrading from 0.6.0:

1. Add explicit source/target revisions to each `Trace`. Put matching outer boundaries
   in `Disclosure.revisions`. Use a fresh owner-assigned version for changed content.
2. Use `ModuleRevision.create` for canonical module snapshots and `snapshot.locate` for
   cross-model references. Local query APIs still accept `EntityRef`.
3. Match `Except` from `Trace.compose`. Mixed tracked/untracked stage composition rejects;
   provide consistent boundaries rather than dropping revision checks.
4. Replace evidence subjects with `LocatedEntity`; provide a `claim` and `EvidenceStatus`.
   Store tool/certificate/revision provenance when available. Protocol 1 reports/traces
   are not silently upgraded because their missing revision identity cannot be inferred.
5. Use `buildIndex` for a derived raw view, or `index` when structural validation is
   required. Neither private hash storage nor serialized proof terms are a public contract.

Existing module wire-format-1 data needs no schema migration. Source API compatibility,
wire compatibility and interop compatibility are independent. The safety break and its
rationale are recorded in ADR 0009 and `api-stability.md`.

## Conformance and external consumers

`Tests/Conformance/Wire/v1` publishes eight positive fixtures plus invalid vectors and a
manifest with canonical fingerprints and rejection codes. They cover hierarchy, symbolic
parameters, acausal structure, nested operations, requirements, geometry-like data, Unicode/control escaping and large integers.
The normative wire specification is sufficient to implement these without Lean deriving.
Full JSON round-trip correctness is tested, not claimed as a kernel theorem.

`Tests/ExternalBackend` imports only `Synthesis`: it defines private contracts, a typed
literal adapter, a tiny target AST, concrete-width prerequisites, revisioned lowering,
independent structural translation validation and separate artifact encoding. Symbolic
widths and unsupported operations reject. This is a conformance fixture, not an HDL tool.

`Tests/ExternalPhysical` supplies symbolic/acausal equation projection and a private
geometry/layer/technology projection. Unsupported or incomplete layout data rejects.
Existing target tests retain placement/hierarchy and systems/requirements coverage.
`Tests/ExtensionComposition` covers four explicit packages, private namespace contracts,
collisions, unknown contracts, nested mixed operations and rejection ownership.
`Tests/RevisionIntegrity` covers B1/B2 mismatch, migration execution, evidence protocol,
source map revision mismatch and scoped navigation. Public import checks cover all three
external-consumer modules. `Tests/Scale` generates 100/1,000-definition CI cases.

## Assurance and remaining pre-1.0 risks

- Logical revision IDs depend on their owner's non-reuse discipline. FNV is not
  collision-resistant; adversarial/distributed identity needs a reviewed cryptographic
  scheme. A digest is not semantic identity or authenticity evidence.
- Trace boundary checks do not prove engineering correspondence or validate every target
  locator. External target packages own locator meaning and preservation relations.
  Historical edges are retained as reports, not promoted to certified history.
- Definition indexing is proved correct; local member lookup, contract/source filtering
  and parts of structural validation still scan lists. Million-entity validation and deep
  operation/attribute workloads are not performance-qualified by the wide-model tests.
- Frontend infrastructure supports domain DSLs but does not automatically record every
  generated declaration, resolve arbitrary human aliases, or implement an LSP. Source maps
  and generation lineage must be supplied by the responsible frontend.
- Protocol records report evidence; they neither check an external certificate nor serialize
  a Lean proof. Translation fixtures prove their stated structural relation, not digital,
  physical or manufacturing correctness.
- JSON parser/whole-codec correctness, trace-list associativity, and all decoder resource
  limits have no universal proof. Fixtures and runtime tests cover concrete cases.
- In-repository consumers are not independent adoption. A non-Lean wire implementation,
  real external pipelines and release-to-release dogfooding remain 1.0 entry criteria.

See `pre-1.0.md`, `benchmarks.md`, `wire-format-v1.md`, `interop-protocol-v2.md` and
ADR 0009 for the corresponding contracts and limits.

## Verification

Commands executed from the repository root:

| Command | Result |
| --- | --- |
| `nix develop --command bash scripts/check.sh` | Exit 0: repository boundaries, `lake build` (2,889 jobs), `lake test`, `lake env lean Tests/Audit.lean`; 133 audited Lean modules |
| `nix develop --command nixfmt --check flake.nix` | Exit 0 |
| `nix flake check --no-build` | Exit 0, host x86_64-linux evaluation |
| `nix flake check` | Exit 0; incompatible Darwin/aarch64 systems were not checked |
| `git diff --check` | Exit 0 |

The proof audit accepts only `propext`, `Classical.choice` and `Quot.sound`. No domain
proofs were replaced by runtime checks. Documentation and final scale results follow.

The optional benchmark runs through `lake env lean --run`, not a calibrated native
performance harness. Times include forcing/output overhead and concurrent documentation
work; they are observations, not throughput guarantees. Two preliminary 100k runs were
interrupted while diagnosing traversal/preflight cost. They are not counted as passes.

Final optional scale runs (both exit 0):

```sh
nix develop --command lake env lean --run scripts/benchmark.lean 10000
nix develop --command lake env lean --run scripts/benchmark.lean 100000
```

| Definitions | Lookup hits | Walk entities | Encoded bytes | Build ms | Lookup ms | Walk ms | Encode ms | Decode ms | Decode |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 10,000 | 10,000 | 20,002 | 3,967,113 | 75 | 29 | 47 | 452 | 15,225 | accepted |
| 100,000 | 100,000 | 200,002 | 39,967,113 | 1,566 | 518 | 754 | 3,352 | 135,847 | accepted |

The 100k run emitted an ignored Nix evaluation-cache SQLite contention message while
another Nix invocation ran; the Lean benchmark completed successfully. Decode time is
still substantial. This is evidence for bounded wide-model operation, not an assertion
of production-scale latency or constant memory. Runtime CI round trips additionally
compare decoded models with their inputs; the optional runner prints acceptance/timing.

`nix develop --command bash scripts/docs.sh` completed with exit 0 on the final Lean
sources: 111 project modules generated, 112 public API pages and search data verified.
`nix develop --command python3 scripts/check_repository.py` also passed after the final
documentation/fixture additions. These verification results precede the release commit. Documentation deployment remains
a separate CI action gated by the repository checks.
