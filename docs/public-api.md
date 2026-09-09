# Public API map

| Import | Main contracts |
| --- | --- |
| `Synthesis.IR` | EntityRef, ResolvedEntity, Module.resolve, walk, walkHierarchy, foldDefinitions, Index, ExtensionPackage, combineMany, encode/decode, Diagnostic.render |
| `Synthesis.Design` | Model, Encoding, AttributeCodec, System, Specification, TechnologyContext, RealizationProblem, CertifiedRealization |
| `Synthesis.Interop` | Requirement, Checker.and, Stage.requiring, Migration, TranslationValidator, CertifiedTranslation, EvidenceReport, ProofEvidence |
| `Synthesis.Frontend` | DesignBuilder, DefinitionHandle, Reference, resolveReference, SourceDocument, existing engineering DSLs |

Locators are module-revision-relative. Definition-table traversal emits named scoped
addresses. Hierarchy traversal emits occurrence paths below the root. Transformations
must remap addresses when renaming declarations or changing argument/attribute order.
Requirements represented by operations use their operation address and private
semantic contract; no core requirement-kind enum is needed.

The initial derived index is an array snapshot, with a theorem that definition lookup
agrees with canonical lookup. It is not yet an asymptotically faster lookup structure.
Its storage fields are private; an optimized implementation must preserve the theorem
and public result semantics. Canonical IR remains the source of truth.

Extension composition requires disjoint ownership manifests. Each contract has one
owner, independent of whether its handler accepts a specific payload. A rejected
payload cannot fall through to another extension. Package identity and contract
namespace ownership remain conventions; no central registry exists.

EvidenceReport records a report with an open method identity. It cannot inhabit a
proposition. ProofEvidence and CertifiedTranslation require Lean proofs. A checked
external certificate can produce a proof only through an explicit verified checker;
external tool success, tests and empirical observations remain reports.

Migration stages compose only when their intermediate schema labels agree. The
source and target Lean types and stage checkers establish actual representation
requirements; numeric labels alone do not prove conformance. Disclosures describe
information movement, while Establishes and semantic relation theorems prove facts.
