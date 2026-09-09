# ADR 0007: Open engineering IR, schema 3

Status: accepted for API 0.5.0 (experimental).

## Audit of schema 2

The initial checkout was clean. Its baseline `nix develop --command bash scripts/check.sh`
passed: 79 modules, build, runtime regressions and assumption audit.

The compiler path was `Frontend.Design.lower → IR.Technology → IR.Validated`.
`Design` duplicated the graph fields. `compileModel` supplied an external interpretation.
`IR.AST` owned Domain, Direction, PortType, Port, Component, Endpoint, Connection,
Technology and Validated, plus all executable structural checks. Domain had built-in
cases plus custom strings; PortType had quantity, quantum and custom constructors.
Component mixed instance identity, operation identity, interface and rational coefficients.
Endpoint used two strings. Connections were exclusively directed pairs. Technology
had no definition sharing, hierarchy, symbolic binding, expression bodies or sufficiency
contract. WellFormed proved connection compatibility from the Boolean validator.

Core.Parameter held dimensional rational literals. Core.Dimension also held a separate
dimension-indexed Expr (integer literal, string symbol, addition, multiplication).
Physics.Quantity, Equation and Balance were scalar-parametric. Logic.Contract supplied
relational behavior, assumptions, guarantees, refinement and feasible composition.
Systems supplied transition relations, reachability, invariants and simulation.
These independent mathematical abstractions are valuable and survive.

Semantics.Interpretation mapped complete components and edges to optional global
behaviors. Model required coverage; Verified required feasibility and conditional
correctness. PreservingPass only supported equivalent endomorphisms. Primitive wrapped
one component, with a full-record recognizer. Domains.Components and Electrothermal
were the central consumers of that adapter. They exposed calculated quantities as
input/output ports, even when the underlying theory was relational. Exact electronics,
thermal, mechanics, photonics, chemistry and quantum certificates used Primitive.verify.
The analytic electronics package already had terminal relations, network conservation,
continuous trajectories and device theories independent of the compiler graph. Those
proofs do not depend on AST layout and must not be rewritten merely to change the IR.

Public callers were the kernel umbrella, the two Examples modules, Tests.Main,
Tests.Formal, Tests.Engineering and Tests.Electronics.Exact. The remaining electronics
regressions primarily exercise mathematics. Tests.Audit imports the transitive project
closure and collects assumptions. check_repository.py enforces closure, source policy,
acyclic imports, kernel/domain boundaries and dependency pins. CI gates Pages on proof
checks and verified generated pages. Documentation tooling is a separate Lake project.

## Decision

Replace the universal flat graph, without retaining a schema-2 compatibility stack.
The canonical boundary is IR.Module. Its orthogonal structures are scoped Definition,
Instance, Port, Junction, Operation, Term, TypeExpr, Attribute and Provenance. Definition
identity is qualified and separate from local Symbol and versioned ContractId. No domain,
backend, type-family or operation-family enum is part of the extension contract.

An operation has a lexically scoped nested body because dynamics, conditional processes
and domain structures require nested binders. Its interpretation is extension-owned.
The minimal recursive Data vocabulary is an interchange encoding, not an engineering
ontology. Domain types and operations use versioned contracts and inspectable arguments.
No Lean closures enter the erased IR. Exact rational data is retained; it is not the
only possible scalar representation. Affine source units and physical kinds are explicit
rich structures. Encoding carries an exact round-trip obligation.

Lean source types, local state spaces, relations and contracts remain authoritative in
Design.Model. Lowering requires an explicit denotation relation. Requirements have
inspectable declarations and retention evidence. They do not become proved merely by
being present. Compiler-facing interpretation covers the complete module; composition
of local relations uses explicit observation projections. Unknown data is never True.

Validation stages are distinct: structural resolution, extension typing, semantic
coverage, and requirement verification. Extension callbacks are explicit configuration,
not a global registry or open-ended instance search. Unknown data may be transported
structurally but cannot cross extension/semantic boundaries without an explicit handler.

Compilation stages can change both representation and observation spaces. Equivalence,
refinement and postconditions are orthogonal to executable Stage. Refinement does not
imply feasibility. Exporter requires a source-indexed proposition and an evidence-returning
checker. Disclosure records assumptions, derivation, erasure and obligations; composing
stages does not infer end-to-end preservation from concatenated claims.

## Consequences

Breaking names, constructors and schema are intentional. Exact domain theorems survive;
their adapters now expose relational observations instead of fictitious causality.
Conservative terminal models are a distinct interface with explicit junction laws.
No target backend, solver, registration service or automatic physical realization is
introduced. Recursive structural hierarchy is rejected; dynamic recurrence belongs in
behavior. Flattening, causalization and discretization require explicit future stages
and preservation results. No flattening theorem is claimed without an implementation.


## Adapter and public-module migration

The public IR, Semantics, Design, Frontend and Interop umbrellas expose the new extension
boundary. Domains.Components is a convenience umbrella over independent Adapters modules;
the existing certificate names survive without a central component registry. The exact
Electronics.Interface demonstrates reusable acausal resistor structure and parameter
binding. Tests.Architecture and Tests.Targets use private contracts through public imports.
Repository checks now enforce the full layer direction, including Design and Interop.
Documentation generation rebuilds its database/site so deleted schema-2 declarations do
not survive in generated pages or search data.


Rich system composition is distinct from the low-level declaration builder:
engineering_system builds typed parts/projections, explicit coupling/constraint relations
and named requirements. Its lowering retains module-level data in wrapper definitions,
root bindings on inner instances and shared child definitions. Conflicting identities
are rejected. compileSystem_preserves proves denotation, without assuming feasibility.
