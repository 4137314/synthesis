# ADR 0009: revision integrity and independent wire contracts

Status: accepted for API 0.6.1, interop protocol 2. IR schema 3 and wire format 1 remain unchanged.

## Audit

Base: b4a08820801b3aa6c8a9fd75ab69c6700f9e1e07. The worktree was clean.
Trace compared module-relative EntityRef values without revision identity. Stage
composition concatenated trace edges without validating an intermediate revision.
Index used an array converted back to a list. Module.walk accumulated growing prefixes.
The JSON representation was defined by derived instances, and decoding could lose
duplicate keys before checking fields. Evidence subjects were local-only references.
Frontend source helpers existed but no reusable explicit name/type elaboration context.
Existing mathematical meanings of refinement, verification and realization were coherent
and remain unchanged. No obstacle required changing the canonical schema.

## Decisions

RevisionRef combines explicitly owned logical identity/version with optional ContentDigest.
LocatedEntity adds this revision to an EntityRef. ModuleRevision computes and caches a
wire-derived fingerprint with a correspondence proof. FNV-1a-64 is provided only for
noncryptographic change detection; security-sensitive content addressing needs an
appropriate independently identified scheme. No collision-free hash axiom is asserted.

Trace owns source/target revisions even for empty entity sets. Checked composition
rejects intermediate revision mismatch. Stage disclosures carry explicit boundaries;
untracked stages cannot smuggle traces into composition. Trace is the end-to-end view;
history retains the original edges. Metadata is not a semantic preservation proof.
Migration stage composition uses the same checks. EvidenceReport subjects are located,
with explicit outcomes and tool/input/output/certificate provenance.

Wire format 1's existing layout is now explicitly encoded/decoded and specified in
wire-format-v1.md. Public record layout is not derived. Field sets, sum tags, exact
rationals and all empty/optional fields are checked. Duplicate JSON keys are rejected
before the parser coalesces them. Golden fixtures retain canonical byte compatibility.
Protocol 2 independently specifies revision-qualified trace/evidence exchange.

Hash indexes remain derived. Definition and entity lookup agreement is kernel proved;
canonical iteration order does not come from hash-map iteration. Raw buildIndex is
separate from validated index construction so validated consumers do not repeat checks.
Traversal avoids growing-prefix accumulation and uses a shared definition table for
hierarchical expansion. Benchmark timing is observational, never a semantic test.

## Compatibility

0.6.1 deliberately repairs a trust-boundary defect before a stable release. Trace
construction requires two revisions, Trace.compose returns Except, and EvidenceReport
requires revision-qualified subjects, status and claim identity. Existing schema-3
module bytes remain format-1 compatible. No project axioms, backend registry, domain
ontology or solver is added. Fingerprints and metadata do not prove artifact correctness.
