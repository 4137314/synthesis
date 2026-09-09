# Architecture

Synthesis is a Lean-native formal engineering frontend and extensible semantic IR
foundation. Independent packages own engineering dialects, refinement pipelines and
artifact production. The core does not know which external formats exist.

## Representation stack

| Layer | Public modules | Meaning |
| --- | --- | --- |
| Mathematical foundations | Core, Physics, Logic, Systems | Dimensions, kinds, scalars, relations, contracts, transitions and invariants |
| Rich source | Design.Model, Design.System | Domain-chosen Lean source, interface/state types, behavior, requirements and an explicit lowering/denotation relation |
| Canonical interchange | IR.Value, IR.AST | Serializable-shaped data, open types/terms, reusable definitions, instances, junctions and nested operations |
| Assurance | IR.WellFormed, IR.Extension, IR.Typing, Semantics | Resolved structure, extension typing, interpretation coverage and requirement evidence |
| Construction | Frontend.Builder, Frontend.System, Frontend.Elaborate, Frontend.Inspect | Lean declaration programs, rich-source compilation and inspection |
| Independent pipelines | Interop.Transform, IR.Information | Heterogeneous stages, refinement, sufficiency, loss disclosure and external exporter contracts |

Rich source is authoritative. `Design.Model.represented` relates the behavior of its
source to the interpretation of its lowering. It is not acceptable to maintain two
representations and assume they agree. A compiler may also ingest an independently
constructed IR.Module and explicitly validate/interpret it. That path has no implicit
source-model theorem.

The erased IR contains no Lean functions, propositions or hidden existential payloads.
The rich layer may use real numbers, dependent types, trajectories, sets, functions and
proofs. `Design.Encoding` requires exact encode/decode round trips; it cannot justify
rounding arbitrary real values into rational literals. A versioned reference JSON encoding is implemented; decoding returns raw IR and requires
separate validation. See [serialization](serialization.md). Decidable equality for recursive data is structurally recursive and
kernel checked.

## Dependency direction

Core is foundational; Logic and Systems remain independent. Physics and IR depend on
Core. Semantics depends on IR and Logic. Design depends on Semantics. Frontend depends
on Design/IR/Semantics; Interop depends on semantic and IR contracts. Domains depend on
these public layers; bridges depend on the domains they couple. Examples/tests are
leaves. The kernel umbrella never imports Domains, Bridges or Examples. Mathematical
electronics modules retain focused imports and their existing theorem decomposition.

## Identity, definitions and hierarchy

`Symbol` is a local identity, `QualifiedId` a sequence of namespace segments, and
`ContractId` a qualified identity plus positive semantic version. A display name belongs
in an annotation. Equality never relies on concatenating textual paths, and no global
registration service is needed. Namespace ownership is a package convention, not an
online uniqueness service.

`IR.Module` owns a definition table, a root definition and root parameter bindings.
Each `Definition` has external ports, local parameters, reusable child instances,
junctions and operation bodies. `Instance` references a definition and supplies local
bindings, attributes and provenance. It does not copy the definition. Separate instance
paths distinguish repeated uses and therefore their local state. `Module.descend?` and
`port?` resolve paths; `ResolvedEndpoint` ties a successful lookup to a particular
module and containing definition. An empty instance path names the current interface.

Finite structural recursion is rejected using a definition-count bound. Dynamic
recurrence belongs in behavior, not recursive structural instantiation. The resolver
supports paths into descendants and exposed ports at the current scope. It does not
implicitly alias an external port to an internal one: use an explicit junction or
extension operation. No hierarchy flattening pass or flattening theorem is claimed.

## Open types, terms and extension data

`TypeExpr` is an application of an extension-owned constructor to inspectable `Data`.
This supports scalar models, finite widths, arrays/tensors, record descriptions,
quantity kinds, interface types and private types without adding a central constructor.
Data's small recursive encoding vocabulary (exact rational/integer/text/symbol,
sequence and tagged data) is not an engineering ontology. An external contract can
encode richer values using these constructors.

`Term` has typed literals, local variables and open operation applications. `Parameter`
records a declared type and optional initializer. Initializers are checked in declaration
order, making dependencies explicit and rejecting forward references/cycles. Instance
bindings are checked in the parent parameter scope. Undefined parameters are legitimate
symbolic inputs; they are not implicitly zero. Operations can bind typed results, which
are visible in their nested body and following sibling operations. Body-local results
do not escape. Duplicate/shadowed binders are rejected.

`Extension` supplies literal recognition, type recognition, application signatures,
port/connector rules, operation-shape rules and semantic attribute recognition. It is
ordinary explicit Lean configuration; private packages compose ExtensionPackage manifests using conflict-checked combineMany.
A signature receives both original arguments and inferred types, so value-dependent
widths/slices need no encoding trick. It can enforce dimension arithmetic, kind distinctions, finite widths or
arbitrary private typing rules. Its laws remain the extension author's responsibility.
`infer_sound` proves that successful inference has an independent `Typed` derivation.
Structural acceptance does not claim that the extension's type system is physically sound.

`Module.concreteParameters` is deliberately conservative: each root/child occurrence
must have literal effective bindings/defaults. A ground application is not automatically
an evaluated coefficient. `Specialized` combines this evidence with extension checking.
Specialization/evaluation algorithms are external stages, not a generic numerical solver.

## Physical quantities and units

`Physics.Quantity Scalar dimension` and the established dimensional theorems remain.
`QuantityKind` adds semantic identity independently of exponents; `KindQuantity` indexes
a scalar by that kind. Stress and energy density need not share a type just because
both have pressure dimensions. Explicit conversion functions must state their laws.

`AffineUnit` records scale and offset separately, requires nonzero scale and normalizes
exact rational source values. It supports affine temperature coordinates without
pretending the offset is multiplicative. Source/display unit data can be retained in
attributes/provenance; no implicit unit inference or real-number approximation occurs.
The library does not supply a comprehensive unit catalog or unit conversion solver.

## Interfaces and connectivity

Every port has an interface contract, open type, extension-owned role and semantic
attributes. There is no universal input/output direction. `Standard.observable` is a
variable in a relation, explicitly distinct from a physical terminal or causal signal.

Junctions have arbitrary endpoint lists. The reusable `IR.Connector` policies provide:

- signals: one producer, multiple sinks and exclusive endpoint incidence;
- resources: the signal discipline restricted to exactly two endpoints;
- conservative terminals: homogeneous multiway interfaces without a producer.

These are optional policies. A custom connector may implement completely different
rules. Matching types/dimensions never creates a physical coupling. Cross-domain bridges
own their equations and explicit interface mapping. Extensions must account for all
hierarchical resource behavior, including operation-internal duplication; a local
incidence check alone is not a quantum no-cloning theorem.

`Semantics.Conservative` states equality of across variables and signed through balance
for a list of terminals. Scalar/quantity choices and orientation are explicit. It is
a mathematical law definition; `balanced` projects its balance consequence, not a proof
that an arbitrary physical junction obeys it.

## Behavior and requirements

`Logic.Behavior α := α → Prop` remains the semantic foundation. α can be a state,
interface valuation, trajectory, field or assembled history. `LocalRelation` allows
each component its own local observation space and an explicit global-to-local map.
`assemble` conjoins pulled-back relations; feasibility is not inferred from conjunction.

An `Operation` carries a contract, terms, result declarations, semantic attributes,
provenance and a nested operation body. Extensions can define equations, constraints,
initialization, derivatives, transitions, guards, resets, modes, algorithms, requirements,
fault alternatives, operating envelopes or geometry. They must define the interpretation:
a name such as “derivative” alone proves nothing. Algebraic and acausal relations do not
need executable causality. No universal equation language, DAE solver or causalizer is
smuggled into the kernel.

`Design.Requirement` pairs a Lean contract with an inspectable declaration and provenance.
`requirementsRetained` proves declaration retention in lowered IR; it does not prove
that arbitrary requirement syntax correctly encodes the Lean contract. An exporter that
needs that relationship must require an interpretation/encoding theorem as well.
Envelopes and uncertainty sets are ordinary admissibility predicates, not an implicit
claim of global applicability. Fault modes are domain-defined alternatives/relations.

## Assurance boundaries

| Value | What it establishes |
| --- | --- |
| IR.Module | Represented data only |
| IR.Validated | Supported schema, scoped identities, finite hierarchy, resolvable junction endpoints |
| IR.Checked extension | The selected extension accepts types, expressions, interfaces, bindings, operations and attributes |
| Semantics.Model observation | A complete module has a supported interpretation |
| Semantics.Verified model requirement | Feasibility in the assumption envelope and universal conditional correctness |
| Interop.Requirement source evidence | Precisely the proposition a consumer declared about this source |

`Module.diagnostics_iff` links empty structural diagnostics to the structural predicate.
`Validated.endpoints_resolve` proves every accepted junction endpoint resolves. `Typed`
is a propositional typing judgment with executable inference soundness. No generic
validator proves a domain's laws or discharges constraints merely by recognizing them.

An interpretation receives the complete module, including attributes, bindings, bodies
and junctions. Unknown input returns `none`, not True. Exact primitive recognizers
compare the complete module. `unsupported` rules out behavior for missing semantics.
Coverage is distinct from feasibility: contradictory laws can be covered but cannot
obtain Verified. The certificate does not establish universal input receptiveness,
liveness, empirical validity or industrial certification.

## Transformations, information loss and external consumers

`Interop.Stage A B` can change representation type and returns either structured
diagnostics or a result with disclosure/trace data. Stages compose with `andThen`.
`Establishes` specifies a postcondition of successful execution;
`andThen_establishes` composes those postconditions through the intermediate result.

`Refines concrete abstract observe` is forward behavioral inclusion. `Equivalent` adds
lifting of every abstract behavior. `RefinementCertificate` separately requires concrete
feasibility in an envelope. `Refines.satisfies` transfers abstract requirements under
the observation map. Existing equivalent `PreservingPass` remains a useful specialization
for model endomorphisms, including feasibility-preserving certificate transfer.

A stage's disclosure records consumed, derived, assumed, preserved and erased contracts,
obligations and many-to-many lineage. These descriptions are not proofs. Composition
retains accumulated losses/assumptions/obligations and trace edges but intentionally
makes no end-to-end preservation claim without a theorem. Rich `Obligation` values
carry Lean propositions separately from diagnostic explanations.

`Exporter Source Artifact` supplies a target contract/version, a source-indexed
requirement, an evidence-returning checker and an evidence-gated emitter. No target
registry or backend implementation exists in Synthesis. External artifacts are not
trusted automatically. See [backend development](backend-development.md).

An abstract electrical model cannot become layout by relabeling a node. A consumer must
require geometry, layers, coordinates and whatever other information it needs; absent
data means a precise rejection or an explicit information-producing refinement. The
same applies to causal digital behavior, electrical node equations, material regions,
meshes, clocks, timing and manufacturing details. Extension data survives until a stage
explicitly projects or erases it; the core never strips unknown attributes silently.

## Frontend and inspection

`engineering_system id where ...` constructs a rich Design.System. `place` composes
already covered models with inferred local observation types and explicit projections;
`couple` supplies junction relations; `constrain` attaches relational laws and inspectable
operations; `require` retains named contracts. The source semantics is the conjunction
of those typed models and explicit laws. `compileSystem_preserves` relates the compiled
model back to that source behavior; feasibility remains a separate obligation.

Rich lowering retains each child module through a wrapper definition and an inner `body`
instance. Module attributes/annotations/provenance remain on the wrapper, root bindings
remain on the inner instance, and identical definitions are shared. Conflicting IDs are
retained for validation to reject. `Design.endpoint` constructs the wrapper-aware path.
This explicit boundary avoids discarding metadata or confusing module and definition
scope. See Examples.Assurance.pairedInventory for a compiled typed composition with a
relational constraint.

The lower-level `engineering id where ...` is an embedded Lean declaration program over `Builder`.
Parameters, ports, instances, junctions and operations have combinators; domain functions
can add arbitrarily rich declaration groups, and Lean macro syntax is extensible without
editing a central parser. It does not duplicate the IR record field by field as a second
Design structure. Domain-rich Lean records lower through explicit functions and proofs.

`#engineering.ir`, `.hierarchy`, `.interfaces`, `.operations`, `.diagnostics` inspect
results. `#engineering.check` generates a kernel-checked structural obligation. Source
spans can be attached by domain syntax/builders; the base combinators do not automatically
capture every source position. This is an embedded Lean DSL, not a standalone parser
or a complete natural-language-like engineering elaborator.

## Versioning, tests and remaining implementation work

API 0.6.0 follows the supported/experimental boundary in api-stability.md. IR schema 3 is a deliberate breaking replacement; Module
carries its schema and validation rejects other versions. Contract versions are separate
from package and core schema versions. No migration framework or compatibility graph
stack is retained. See [ADR 0007](adr/0007-open-engineering-ir.md) for the audit/decision.

Architecture tests exercise third-party contracts, shared definitions, hierarchy,
multiway conservative/signal/resource policies, symbolic typing, specialization
prerequisites, scoped failures, private geometry data, sufficiency evidence, local
semantics and a lossy heterogeneous projection. These are infrastructure tests, not
proofs of support for any target format. Exact and analytic domain proofs remain audited. Domains.Components is now only a
convenience umbrella; Adapters.Electronics, Thermal, Mechanics, Photonics, Quantum and
Chemistry have independent imports. Tests.Targets exercises concrete clock/reset/state,
differential, layout/placement, requirement-lineage and FEM-boundary payloads.

Future work includes richer domain-specific surface syntax, complete source-position
capture, additional codecs, scalable indexed lookup, automatic parameter evaluation,
hierarchy flattening and domain-specific refinement proofs. These fit the public
extension/stage contracts; no corresponding implementation or preservation theorem is
claimed today. Solvers, target emitters, physical implementation and manufacturing
realizability belong outside this task.


## Supported API boundary

API 0.6.0 retains IR schema 3. The serialization format is independently versioned at 1,
and the generic interop protocol is 1. See [API stability](api-stability.md) and
[public API map](public-api.md) for supported versus experimental contracts.

EntityRef addresses module-relative definitions, hierarchical occurrences and named
local declarations; arguments and repeated attributes are explicitly positional.
Module.walk provides definition-table preorder; walkHierarchy expands occurrences
with a depth budget. Index is a derived snapshot with a lookup-agreement theorem,
not serialized truth. Consumers should use these queries instead of storage fields.

ExtensionPackage declares exclusive contract ownership. Composition rejects conflicts
before running handlers. An unsupported payload cannot be accepted by falling through
to another owner. TypeFamily, AttributeCodec, OperationSchema and InterfaceSchema help
domain authors build typed APIs without central registration.

Diagnostic subjects and related entities use EntityRef. SourceDocument maps portable
byte spans to zero-based line/byte-column positions. sourced_operation attaches syntax
origin without storing Lean syntax in IR. Full frontend elaboration remains extensible;
these helpers do not promise inference of arbitrary private engineering constraints.

CertifiedTranslation requires a proof of a specified source/target relation.
EvidenceReport remains a report. CertifiedRealization separately requires technology
admissibility, feasibility and specification satisfaction. Migration composes explicit
schema transitions; disclosures are not preservation theorems.
