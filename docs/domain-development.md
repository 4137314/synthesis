# Domain author guide

An external package can `import Synthesis` (or the focused public umbrellas
`Synthesis.IR`, `Synthesis.Semantics`, `Synthesis.Design`, `Synthesis.Frontend`) and define
its own namespace. No core enum, global catalog or registration service needs editing.

## 1. Start with a mathematical model

Choose parameter, interface and internal-state types. A state can be a trajectory,
a field or a nondeterministic history. Use `Design.Definition Parameters Interface State`
for an admissibility predicate and a relation, or retain an existing domain structure.
Use `Logic.Contract` for explicit assumptions/guarantees and `Systems` for transition
invariants/simulation where appropriate. Physical laws are definitions or hypotheses;
prove their logical consequences and state applicability limits separately.

Quantity exponents and quantity kinds are distinct. Reuse `Physics.Quantity` where
only dimensions matter; use `QuantityKind`/`KindQuantity` for semantic distinctions.
Choose the scalar needed by the model. Do not coerce a real-valued model to rational
interchange coefficients without an explicit representation/approximation theorem.
`AffineUnit` normalizes rational source coordinates with separate scale and offset;
retain the source unit as identified metadata when a consumer needs it.

## 2. Define contracts and data encoding

Use `ContractId.named "acme.hydraulics" "terminal" 1`, for example. The owner string is
one namespace segment, not a parser for dot-separated global paths. Contract version
changes whenever the meaning/encoding changes. Local entities use Symbol; reusable
definitions use QualifiedId segments. Never encode changing coefficients solely in an
unchanging operation identity.

Create `TypeExpr` constructors with inspectable Data arguments for your types, arrays,
fields, dimensions, geometry or control disciplines. Define typed rich records for
complex payloads and explicit encoders/decoders. `Design.Encoding` can certify exact
round trips. Unsupported or malformed values must be rejected by the decoder/validator.
No central AST constructor is needed for a new type family.

## 3. Define interfaces and laws

A port combines an interface contract, type and role. Roles are your own contracts.
Signal, conservative and resource incidence helpers in IR.Connector are optional.
A hydraulic connector might use across pressure and signed through volume flow. Its
mathematical interpretation can instantiate Semantics.Conservative with the chosen
quantity types. The generic incidence check does not prove that conservation law.

A bridge must explicitly relate both domains. Equal dimensions do not authorize a
cross-domain coercion. Quantum resource incidence must also account for behavior bodies
and hierarchical boundary discipline; graph validation is not a quantum gate theorem.

## 4. Build reusable definitions

This complete program uses only the public API:

```lean
import Synthesis
open Synthesis Synthesis.IR Synthesis.Frontend

def hydraulicTerminal : Port :=
  ⟨"terminal", .named "acme.hydraulics" "conservative",
    ⟨.named "acme.hydraulics" "terminal-state", []⟩,
    .named "acme.hydraulics" "terminal", []⟩

def valve : Definition := engineering ⟨["acme.hydraulics", "valve"]⟩ where
  port hydraulicTerminal
  parameter ⟨"opening", Standard.rational, none⟩
  operation (Standard.relation "envelope"
    (.named "acme.hydraulics" "opening-admissible") [.variable "opening"])

def pair : Definition := engineering ⟨["acme.hydraulics", "pair"]⟩ where
  instanceOf "left" valve.id [⟨"opening", .literal Standard.rational (.rational 1)⟩]
  instanceOf "right" valve.id [⟨"opening", .literal Standard.rational (.rational 0)⟩]
  junction "node" (.named "acme.hydraulics" "conservative")
    [⟨["left"], "terminal"⟩, ⟨["right"], "terminal"⟩]

def hydraulicDesign : Module := design pair [valve]
#engineering.check hydraulicDesign
```

This establishes structure only. The opening-admissible operation still needs both a
typing handler and an interpretation. The two valve instances reuse one definition.
Parameters can bind to parent parameters and derived terms. Defaults are declared in
dependency order; cyclic/forward references fail typing. Unbound parameters remain
symbolic. A consumer can additionally demand concreteParameters.

## 5. Implement extension checking

Construct an `IR.Extension` value. Recognize complete types, literals, application
signatures, ports, junctions, operations and semantic attributes. Return false/none for
unknown input. Do not make a catch-all “recognized” branch merely to pass tests.
Inspect nested-body shape in the operation callback; the generic checker separately
checks nested expression typing and lexical scope. Connector callbacks see the module
and definition so they can check incidence/ownership beyond one endpoint pair.

Add contextual diagnostics in `explain`; the core also reports structural scopes,
unresolved paths, rejected ports and connector endpoint types. Extension.accepts is an
executable typing/coverage policy, not a proof of its physical correctness. Successful
expression inference has a `Typed` proof through `infer_sound`. Additional dialect
soundness theorems belong in your package.

See Tests.Architecture for a complete explicit extension configuration with accepted and
rejected literals, applications, symbolic bindings, signals and hydraulic junctions.
It imports only Synthesis, demonstrating the private-package boundary.

## 6. Relate rich source and erased IR

Provide `Semantics.Interpretation Observation`. It interprets the complete module,
including bindings, junctions, attributes and behavior bodies. A decoder may assemble
local relations using `LocalRelation` projections. Return none for any unsupported
construct. Do not silently ignore a semantic attribute because it is inconvenient.

Package the rich source, its lowering, its relation, interpretation and denotation proof
in `Design.Model`. Attach requirement declarations and prove they are retained. Then
`Frontend.compileModel` checks structure and produces a covered model;
`compileModel_preserves` transfers the source relation. If you need extension typing as
well, require/check `IR.Checked extension` explicitly.

Use `Semantics.Verified` only with a feasibility witness in the assumption envelope and
a proof of all conditional guarantees. A syntactically retained requirement is not a
certificate. `Frontend.Certified` proves only its explicit graph predicate. Rich
requirements and erased declarations need a separate encoding/interpretation theorem
if a consumer relies on their precise correspondence.

Synthesis.Examples.Assurance is a complete rich-model/certificate example. The migrated
Domains.Components preserves exact single-model certificates using full-module
recognizers. Electronics.Interface adds reusable terminal structure and explicit
constitutive equations without causalizing the resistor. Existing analytic electronics
remains a source of independent relational/dynamic/network theorems.

For typed composition, use `engineering_system ... where` with `Frontend.place name
model projection`, `couple`, `constrain` and `require`. It returns a rich Design.System,
not an erased definition. Each placed model retains its own observation type. The
lowering shares identical definitions and retains child module metadata/root bindings
through explicit wrapper scopes. `Frontend.compileSystem_preserves` proves the resulting
model has the source conjunction of behaviors and supplied laws. Duplicated placement
names or conflicting definition IDs fail structural compilation. See
Examples.Assurance.pairedInventory for a complete example. These composition semantics
do not infer joint feasibility or physical coupling from topology.

## 7. Extend behavior and syntax

Use open operation applications and nested bodies for algebraic equations, DAE relations,
state transitions, initialization, guards/resets, fault alternatives and geometry.
Nothing forces causality or executability. Define the signature, interpretation and
admissibility of every new construct. An uncertainty set is a predicate, not necessarily
an interval. Operating envelopes remain explicit assumptions.

Builder is an ordinary Lean declaration program. Domain functions can add several
ports, parameters, equations and attributes at once. Domain macros may extend Lean
term/do syntax without editing Synthesis's parser. Introspection commands show IR,
hierarchy, interfaces, operations and structural diagnostics. SourceSpan/Provenance can
be populated by your syntax layer; automatic per-declaration source capture is not yet
provided by the base DSL.

## 8. Refinement, testing and publication

Use Interop.Stage for representation-changing work; state postconditions with Establishes
and behavioral guarantees with Refines/Equivalent. Add feasibility separately for
refinement certificates. Retain unknown data or disclose/prove a deliberate projection.
Record assumptions, erased information, obligations and lineage. Never claim target
sufficiency without checking the actual prerequisites.

Add positive and negative regressions for malformed payloads, names/scopes, dimensions,
kind mismatches, unsupported constructs, constraint violations and infeasible relations.
Document new physical models in docs/models.md with assumptions and theorem names.
Use explicit Lean variables and English text. Kernel code must not import your package.
Run the repository proof, module-closure and assumption audits; no proof holes or
project-specific unchecked assumptions are permitted.
