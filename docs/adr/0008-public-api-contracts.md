# ADR 0008: logical public APIs above canonical storage

Status: accepted for API 0.6.0.

The 0.5 audit found canonical record constructors and List fields exposed throughout
examples, inspectors, validators and external-style tests. Module.definition? and
Module.descend? provide useful shared lookup but there is no general entity query.
Operation bodies are manually unpacked in each consumer. Extension callbacks are
explicit and fail closed, but composition and ownership conflicts are left to callers.
Trace identifies only qualified definitions. Diagnostic has source offsets but no
fine-grained subject or related entities. SourceSpan stores offsets, not a source map.
No canonical serializer, schema migration or translation validator is implemented.

Retain schema 3's logical declarations. Public query results are snapshots: consumers
must not infer mutable storage or cache identity from them. Derived indexes must carry
an exact source relation. Named declarations are addressed by their scoped names;
argument positions and repeated attribute occurrences are explicitly positional.
Entity references are relative to a module revision, not globally unique object IDs.
Transformations must remap references when editing identities or positional schemas.
Requirements encoded as operations use operation locators; their semantic contract
identifies them as requirements without a core engineering ontology.

The API stability policy will distinguish supported query/semantic contracts from
experimental frontend elaboration and storage-oriented constructors. Portable data
cannot carry Lean proof closures. Evidence about a portable representation must remain
indexed by that representation or be independently checked after decoding.


Implementation: IR.Entity/Query/Index separate addresses, logical traversal and derived
storage. IR.Composition requires disjoint manifests rather than last-wins dispatch.
IR.Serialization format 1 preserves schema-3 data and rejects unknown record fields.
Interop.Validation separates proof-producing validation from reports and defines
explicit migration composition. Design.Realization states admissibility and feasible
satisfaction. Frontend.Scope/Source/Construction provide snapshot-bound references,
source navigation/capture and transactional construction.

The canonical module schema remains 3: no declaration payload was changed. Diagnostic
and Trace source APIs break deliberately: fine-grained locators are now supported,
and Trace source/target lists use EntityRef rather than QualifiedId. The reference
wire format is 1 and generic interop protocol is 1, independently of API 0.6.0.
No promise of efficient million-entity queries is made by the initial array index.
No JSON round-trip theorem is claimed; conformance checks cover its runtime behavior.
