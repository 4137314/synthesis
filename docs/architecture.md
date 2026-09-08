# Architecture

`synthesis` is a formal engineering compiler frontend, organized around a small
reusable kernel and extensible domain theories. It produces backend-neutral models
and explicit proof obligations. Target code generation belongs to downstream projects.

## Layers

| Layer | Responsibility | Evidence |
| --- | --- | --- |
| Core | SI exponent algebra; dimension-indexed symbolic expressions | Associativity, commutativity, scalar identity |
| Logic | Assume/guarantee contracts and shared-observation composition | Reflexive/transitive refinement, satisfaction transfer, composition |
| Physics | Scalar-parametric quantities, equations, integrated balances | Dimension-safe operations; closed integer balance conservation |
| Systems | Transition relations, reachability, abstraction maps | Invariant induction, simulation and safety transfer |
| IR | Typed components and connections | Executable structural checks; propositional edge compatibility |
| Semantics | Partial interpretations and graph behaviors | Coverage, feasibility, conditional guarantees, pass preservation |
| Frontend | Embedded Lean DSL and semantic compilation | Graph/interpretation preservation |

Dependency rules: Core is foundational. Logic and Systems are independent. Physics
and IR depend on Core. Semantics depends on IR and Logic. Frontend depends on IR and
Semantics. Domain packages build on these layers, never the reverse. The umbrella
`Synthesis.lean` exports the kernel; examples are imported separately.

## Compilation and assurance

`Frontend.Design` → `Design.lower` → `IR.Technology` → `IR.Validated`.

The structural validator checks identifiers, endpoint existence, direction, port-type
compatibility, single drivers, quantum register widths and quantum fan-out. Theorem
`Validated.connections_compatible` connects the executable checker to a propositional
specification: every edge resolves to correctly directed ports of equal types.
Component parameters have nonempty unique names, a dimension tag and an exact rational
literal. Structural checks do not establish domain-specific coefficient admissibility.
Cycles and unconnected ports are allowed and carry no implicit physical meaning.

`Frontend.compileModel` additionally requires an `Interpretation` and proof that all
components and connections are supported. `compileModel_preserves` proves the result
retains the source graph and the supplied interpreter. Unknown operations are not
unconstrained nodes: they have no interpreted behavior and cannot obtain a coverage
proof. Interpreters must recognize complete interfaces, not merely names.

`Semantics.Verified model requirement` proves:

- Some model behavior satisfies the assumption envelope (non-vacuity).
- Every model behavior in that envelope satisfies the guarantee.

These are proofs about the interpretation. Validating its physical applicability is
an additional scientific/engineering responsibility. `Frontend.Certified` only proves
a graph predicate and is intentionally weaker than this semantic assurance boundary.

`PreservingPass` packages a transformation with pointwise equivalence of behaviors.
Pass composition preserves both feasibility and conditional requirement satisfaction.
No optimizer is implemented; future passes must supply their own preservation proofs.

## Physical and systemic boundaries

`Quantity Scalar dimension` does not force every theory to use one numerical field.
`Equation` enforces matching dimensions. `Balance` specifies an integrated inventory
balance with generation. Its conservation theorem currently specializes to integers.
`Expr` remains a separate symbolic kernel; symbolic binding and equation elaboration
into the graph are not implemented. Literal rational parameters are carried by components. Units, physical kinds, affine quantities and
numerical errors need stronger domain-specific representations.

`TransitionSystem` is a discrete nondeterministic abstraction. `Invariant.reachable`
proves safety for all reachable states. `Simulation.safety` transfers abstract safety
to concrete systems. Neither theorem proves liveness, continuous-time fidelity or
robustness to unmodeled disturbances.

Contract conjunction shares observations. Compatibility requires a feasible joint
behavior under both assumptions; it is not inferred from two independent certificates.
A feasibility witness does not prove realizability for every input.

## Consumer contract and evolution

Consumers import `Synthesis` and choose the evidence level they require: structural
`IR.Validated`, interpreted `Semantics.Model`, or `Semantics.Verified` for a named
requirement in their own requirement catalog. Consumers must reject operations they
do not implement. Graph schema version is 2; package/API version is 0.3.0.

No parser, serializer, universal solver, domain simulator or backend is provided.
Rational literal parameters are implemented. Priorities include scoped symbolic equations, structured
diagnostics, hierarchical composition, domain-specific theories, versioned interchange
and verified elaboration/optimization passes. Each extension must state what is proved
and what remains assumed. See [domain development](domain-development.md).

## Domain catalog and dependency enforcement

`Synthesis.Domains` exports electronics, thermal, mechanics/materials, photonics,
chemistry and exact elementary quantum models, plus parameterized primitive adapters.
`Synthesis.Bridges` exports explicit domain couplings; the initial bridge is an ideal
Joule heater. The kernel does not import these umbrellas. See [models](models.md) for
the exact definitions, theorem inventory, sources and limitations.

`Semantics.Primitive` packages a single component, its relation and structural evidence.
It recognizes the complete component, including rational parameters. Its `verify`
theorem constructs a requirement certificate from feasibility and domain correctness.
Domain primitives currently have no edges; network composition still needs coupling
semantics and compatibility evidence.

`check_repository.py` verifies import closure, cycles, layer boundaries and source policy.
`Tests.Audit` transitively imports every project module and checks proof assumptions.
New modules omitted from that closure fail CI rather than escaping the audit.

## Mathematics and documentation dependencies

Mathlib is pinned to the Lean 4.32.2 release and used by `Domains.RealElectronics`.
The computable rational models retain their existing scalar semantics. Real-valued
coefficients require a future explicit representation/approximation boundary to enter
the rational AST. No implicit rounding is introduced.

API generation uses doc-gen4 in the separate `docbuild` project. Its manifest shares
the root dependency pins, which repository checks enforce. The CI workflow builds
and audits the library before publishing generated pages from main to GitHub Pages.
See [documentation maintenance](documentation.md).
