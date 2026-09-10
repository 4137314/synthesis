# External compiler and lowering author guide

Synthesis supplies contracts, not backends or a registry. An independent package can
import Synthesis.Interop and Synthesis.IR, choose a source representation, and own its
entire lowering pipeline. Private formats and future dialects need no upstream change.

## Choose the actual source boundary

Use IR.Module for inspection, IR.Validated for resolved finite structure,
IR.Checked extension for an accepted dialect, or Semantics.Model for interpreted behavior.
For a certified export, require Semantics.Verified for the particular model/requirement,
and any representation/traceability theorems needed by the artifact. These evidence
levels are different; structural validity is not semantic coverage or physical validity.

A stage can consume a domain's strongly typed model rather than canonical IR. Stage A B
and Exporter Source Artifact do not require equal source/target types or observation
spaces. Target-specific representations belong to the external package. Interchange
uses schema 3; check core schema and every dialect contract version you rely on.

## State information sufficiency as a proposition

Define `Interop.Requirement Source` with a versioned identity and `holds : Source → Prop`.
Then implement `Checker requirement`, returning either a proof of holds for the actual
source or structured diagnostics. The checker may be executable, or a project may use
previously established Lean evidence for conditions that are not decidable automatically.
A Boolean feature label without a meaningful predicate does not establish sufficiency.

Examples of prerequisites (not implemented target support):

| Target class | Information a consumer may need |
| --- | --- |
| HDL | Finite bit widths, module hierarchy, clock/reset discipline, supported causal combinational/sequential behavior |
| SPICE | Electrical terminals/nodes, conservative coupling, constitutive models and concrete supported parameters |
| Modelica/FMI | Equation/DAE relations, state/initialization, units, causality choices at the appropriate stage |
| GDSII/OASIS | Cells, valid geometry, coordinates, layers, placements/transforms, technology conventions |
| SysML-like | Definitions, composition, requirements, relationships and traceability; abstract parameters may remain symbolic |
| FEM preprocessing | Geometry/material regions, boundary conditions and the discretization information the chosen tool requires |

Each package must state its complete requirements. The illustrative polygon checker in
Tests.Architecture proves only its named polygon-information predicate. It is explicitly
not a GDSII sufficiency certificate, manufacturability proof or geometry validity theorem.
It checks contract and coordinate/layer payloads rather than accepting a node named
“geometry”. Missing information yields a scoped diagnostic with remediation.

## Define a preparation pipeline

A high-level model may need several explicit stages before it meets those requirements.
Architectural behavior → RTL → gates → physical placement is a refinement chain, not
renaming. Constitutive equations → causalized equations → numerical representation has
additional applicability, solvability and approximation obligations. The source must
supply information or a stage must derive/refine it under explicit assumptions.

Implement each stage as `Stage A B`, returning an error or `Result B`. State successful
postconditions with Establishes. `Stage.andThen_establishes` composes them with an
explicit intermediate witness. Define source/target behavior and an observation map:

- Refines means every concrete behavior projects to an abstract behavior.
- Equivalent additionally means every abstract behavior has a concrete lift.
- RefinementCertificate adds concrete feasibility in an envelope.
- Refines.satisfies transfers an abstract requirement through the observation map.

These propositions need proofs; the category name “lowering” establishes none of them.
Structural output validity is another independent postcondition. A projection to names
alone may be useful and lossy without being a semantics-preserving compiler.

## Disclose loss, assumptions and obligations

Result.disclosure carries consumed, derived, preserved, erased and assumed contracts,
diagnostics for outstanding obligations and many-to-many trace edges. Retain source
spans, external requirement identities and derivation parents where appropriate.
Semantic attributes affect meaning/lowering; annotations are nonsemantic presentation
metadata. Unknown semantic data must survive or be explicitly rejected/projected.

Disclosures are inspectable descriptions, not proof certificates. Composition accumulates
losses, assumptions, obligations and trace edges but clears preservation claims rather
than guessing an end-to-end guarantee. Give a theorem for the guarantee you need.
Interop.Obligation carries a rich Lean proposition alongside its explanation; diagnostics
alone cannot discharge it. Target packages may return their own richer proof-carrying
result types because Stage is generic in its target.

## Produce artifacts through the gated API

Implement `Exporter Source Artifact`:

1. Set a target contract/version.
2. Supply its Requirement and Checker.
3. Implement emit, whose signature requires evidence that the source meets that requirement.
4. Return the artifact with disclosure/traceability, or precise diagnostics.
5. Optionally prove artifact interpretation, property preservation or requirement traceability.

Exporter.run invokes the checker before emit. There is no core backend list, runtime
plugin loader or requirement to modify Synthesis. The core deliberately provides no
HDL/GDSII/SPICE serializer. Artifact files and external tool results are outside Lean's
trust boundary unless a separate verified relation or checker establishes the needed
property. A backend must never silently fabricate geometry, model parameters, laws,
clock discipline or realizability evidence.

## Test the contract, including refusals

Test supported source fixtures and unsupported versions/types/operations. Test missing
parameters, absent geometry/technology data, wrong quantity kinds, unhandled attributes,
conflicting clocks, invalid ownership and any unsupported behavior subset. Test that a
failed prerequisite never reaches emission and that every lossy path declares its loss.
Add theorem tests for non-vacuity and preservation claims. No generic Synthesis check
can replace a backend's complete implementation-specific sufficiency contract.


## API 0.6 public consumer boundary

Use Module.foldDefinitions, Module.walk, Module.operationsWith, Module.findEntity and
Module.resolve for inspection. walkHierarchy expands instance occurrences with a
caller-selected depth budget and reports exhaustion. Use EntityRef in traces; a
qualified definition ID alone cannot identify a particular port or nested result.
Index.findDefinition has a kernel theorem agreeing with canonical lookup, and uses hash lookup. Do not depend on index storage.

Stage.requiring and Checker.and reuse proof-producing prerequisites before any stage.
Checker.and reports failures from both prerequisites in left-to-right order.
TranslationValidator.certify can certify a target from an untrusted generator against
an explicit relation. This is independent of how the target was produced. An external
success status belongs in EvidenceReport and cannot substitute for its proof.

Trace.compose returns an end-to-end view or revision-mismatch diagnostics. Stage.andThen
checks disclosure boundaries and trace endpoints, stores end-to-end links in trace and
original edges in history. LocatedEntity qualifies external evidence subjects by revision.

Migration.andThen rejects mismatched intermediate schemas. Its stage carries disclosure
and can use Establishes for actual semantic guarantees. Merely declaring matching
version numbers is not a conformance proof. Canonical upgrades must decode the old
format explicitly, execute the migration, and validate the new representation.

See [serialization](serialization.md), [public API](public-api.md) and
[stability policy](api-stability.md). Tests.ExternalPackage is a public-only private
domain/consumer fixture; it deliberately rejects a symbolic source when literal
parameter information is required.
