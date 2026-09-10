# Interop protocol 2

This protocol is independent of canonical module schema 3 and module wire format 1.
It uses the JSON canonicalization, identity and revision encodings specified in
[wire format 1](wire-format-v1.md). No Lean proof closures are serializable.

A trace record has exactly:

- protocol: integer 2;
- sourceRevision, targetRevision: RevisionRef;
- source, target: arrays of EntityRef relative to those respective revisions.

Protocol.encodeTrace/decodeTrace implement this record. Trace.compose returns diagnostics
unless every edge pair agrees on the intermediate revision. Empty edge batches yield no
links. To record a known boundary with no entities, use a Trace with empty source/target
arrays, not an absent trace. Stage disclosures additionally retain boundaries independently
of trace presence; composition validates them and the edge endpoints. End-to-end links
are in trace; history retains original links. Missing revision context is not guessed.

An evidence record has exactly:

- protocol: integer 2;
- id, method, claim: ContractId;
- subjects: LocatedEntity array;
- status: one of "passed", "failed", "inconclusive", "not-run", "assumed";
- tool: ContractId or null (its version is the tool contract version);
- inputs, outputs: RevisionRef arrays;
- certificate: RevisionRef or null;
- statement: string;
- dependencies: ContractId array;
- provenance: schema-3 Provenance.

Protocol.encodeEvidence/decodeEvidence implement this record. Unknown outcomes, versions,
fields and malformed identities reject decoding. Syntactically valid identity data is
retained; namespace ownership and nonreuse of logical revision versions remain explicit
package obligations. A certificate reference points to evidence; it does not check it.
A "passed" report does not establish a Lean proposition. ProofEvidence,
CertifiedTranslation, TracedTranslation and RoundTripEncoder require actual proofs.

Migrations retain their source/target schema labels and use revision-aware stages.
Matching numeric schema labels is insufficient to compose different intermediate
revisions. Semantic guarantees must be established separately with Establishes,
Refines, Equivalent or a package-defined relation.
