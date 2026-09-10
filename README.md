# synthesis

[API documentation](https://4137314.github.io/synthesis/) · [Source](https://github.com/4137314/synthesis)

Synthesis is a Lean 4 formal engineering frontend and extensible semantic IR foundation.
Engineering domains define typed models, behavior, requirements and refinement; independent
downstream packages can lower validated representations into domain-specific and
tool-specific formats.

Synthesis provides the architecture that makes such backends possible; it does not
provide them itself. A target's required information must be supplied or explicitly
derived. An abstract model without geometry cannot be exported as physical layout by
inventing coordinates, and an acausal specification is not automatically implementable RTL.

## Getting started

```sh
nix develop
bash scripts/cache.sh
bash scripts/check.sh
```

Nix pins development tools through `flake.lock`; Elan selects Lean **4.32.2** from
`lean-toolchain`. The first Lean command downloads the compiler and needs network
access. `.elan/` is workspace-local and ignored by Git. This is a Nix development
shell, not a hermetic Nix build of Lean or the library. Lake performs compilation.
Mathlib is pinned to its Lean 4.32.2-compatible commit in `lakefile.toml` and
`lake-manifest.json`. `scripts/cache.sh` downloads its required compiled import closure.
Alternatively, use an existing Elan installation and Python 3 with the same scripts.

Flake files must be tracked by Git for `nix develop` to include them. Direnv is optional
(`direnv allow`). CI also checks Nix formatting with `nixfmt --check flake.nix`.

## Engineering models

```lean
import Synthesis
import Synthesis.Domains
import Synthesis.Bridges

open Synthesis
#check Domains.Components.resistor_passive
#check Domains.Components.capacitor_energy_nonnegative
#check Domains.Electronics.Network.tellegen
#check Domains.Electronics.Nodal.branch_voltage_unique
#check Domains.Electronics.Source.maximum_power_transfer
#check Domains.Electronics.Transient.FirstOrder.natural_unique
#check Domains.Electronics.SecondOrder.overdamped_decomposition
#check Domains.Electronics.Rlc.series_loop_solves
#check Domains.Electronics.Thevenin.affine_unique
#check Domains.Electronics.Power.apparent_sq
#check Domains.Electronics.Filter.lowPass_cutoff
#check Domains.Electronics.Magnetics.Coupled.energy_nonneg_iff
#check Domains.Electronics.TwoPort.Impedance.passivity_iff
#check Domains.Electronics.TwoPort.toImpedance_toAdmittance
#check Domains.Components.optical_conservation
#check Domains.Chemistry.reachable_elements_conserved
#check Domains.Quantum.Gate.preserves_normalization
#check Bridges.Electrothermal.heater_verified
```

| Domain | Initial model | Proved properties |
| --- | --- | --- |
| Electronics (exact) | Resistor, conductor, capacitor, inductor, ideal sources | Passivity, series/parallel algebra, divider identities, stored energy, unique loop operating point |
| Electronics (networks) | Finite topologies, nodal analysis, source and one-port equivalence | Kirchhoff laws, Tellegen's theorem, superposition, solution uniqueness, Thévenin/Norton, uniqueness of the Thévenin equivalent, maximum power transfer |
| Electronics (dynamics) | Storage in continuous time, first- and second-order transients, RLC circuits | Power as the derivative of stored energy, uniqueness of the first-order solution, completeness of the overdamped modes, no real mode below critical damping, circuit equations derived from the element laws |
| Electronics (frequency) | Phasors, sinusoidal power, first-order filters | Resonance minimizes impedance, the power triangle, dissipation only in the resistive part, exact half-power cutoff and monotone roll-off |
| Electronics (devices) | Diode, transistor, feedback, logic levels | Diode passivity, pinch-off continuity, ideal gains as limits, noise immunity |
| Electronics (multiport) | Coupled inductors, ideal transformer, two-ports | Coupling bound equivalent to passivity, lossless transformer and impedance reflection, two-port passivity characterization, T and Π realizations, cascade reciprocity, verified parameter conversions |
| Thermal | Steady lumped conductance | Equilibrium, heat-flow direction, terminal conservation, dissipation inequality |
| Mechanics/materials | Uniaxial linear elasticity | Nonnegative energy density, strict stress monotonicity, uniqueness, work identity |
| Photonics | Incoherent passive power splitter | Nonnegative outputs/loss, power conservation, no gain |
| Chemistry | Finite stoichiometric batches and reaction networks | Weighted inventory and element conservation for reachable states |
| Quantum | X, Z and S on complex-rational amplitudes | Linearity, reversibility, norm preservation and composition |
| Electrothermal bridge | Ideal Joule heater | Electrical-to-thermal power conservation and passivity |

See the [model catalog](docs/models.md) for assumptions, theorem names and source
references. These are exact idealized models, not complete industrial device models.

## Formal boundary

- SI dimensions, scalar-parametric quantities, equations and balance laws.
- Assume/guarantee contracts, refinement and composition.
- Transition systems, inductive invariants and forward simulation.
- Open, versioned IR contracts with reusable definitions, hierarchy and multiway junctions.
- Symbolic typed parameters, nested behavior bodies and identified semantic attributes.
- Explicit component/coupling interpretations and non-vacuous requirement certificates.
- Representation-changing stages, refinement proofs and evidence-gated external exporter APIs.

Proofs are kernel-checked. The audit permits only Lean's standard foundational
assumptions (`propext`, `Classical.choice`, `Quot.sound`), with no project-specific
unproved assumptions. Physical laws are explicit model definitions or hypotheses.
The guarantees apply within those models and hypotheses; empirical applicability,
uncertainty, numerical approximation and industrial certification need additional work.

The API is experimental: **0.6.1**, **IR schema 3**. This is a deliberate replacement of
the old flat graph API. The compiler-facing IR is open data; rich Lean models retain
relations and proofs through explicit denotation links. Independent extensions define
types, interfaces, operation semantics, geometry or lower-level dialects without central
enum changes. Exact rational coefficients remain available without becoming the universal
scalar model. Arbitrary real values are never silently rounded.

The rich `engineering_system ... where` DSL composes typed semantic models, explicit
relations and requirements. The lower-level `engineering ... where` builder supports reusable definitions,
instances, parameters, ports, junctions and extension operations. Inspection and validation
commands show the resulting structure. See the [architecture](docs/architecture.md),
[domain author guide](docs/domain-development.md), [backend author guide](docs/backend-development.md)
and [migration decision](docs/adr/0007-open-engineering-ir.md).

The explicitly specified JSON codec retains format version 1; revision-aware interop uses protocol 2. Fine-grained entity queries, explicit
extension composition and translation-validation APIs are public foundations; see the
[API policy](docs/api-stability.md), [public API map](docs/public-api.md) and
[serialization contract](docs/serialization.md). The [stabilization report](docs/stability-report.md)
records implemented guarantees, migration instructions and remaining risks. See the [wire specification](docs/wire-format-v1.md),
[revision decision](docs/adr/0009-revision-and-wire-integrity.md), and [pre-1.0 criteria](docs/pre-1.0.md).

No target backend, solver, automatic causalizer or verified hierarchy
flattening pass is implemented. Domain-specific syntax, comprehensive source-position capture,
parameter evaluation and concrete lowering stages remain extension work. Structural
validation, extension typing, semantic coverage and requirement verification are distinct.

Electronics is decomposed one module per theory, with an umbrella per directory that
re-exports its parts and maps them, so a consumer that needs only Kirchhoff's laws does
not compile the diode model. See
[ADR 0006](docs/adr/0006-electronics-module-decomposition.md).

## Development

Read [CONTRIBUTING.md](CONTRIBUTING.md), [AGENTS.md](AGENTS.md), the
[architecture](docs/architecture.md), and the [domain extension contract](docs/domain-development.md).
All repository prose and identifiers are maintained in English. CI checks module
coverage, dependency boundaries, builds, regressions and transitive proof assumptions.

## API documentation and GitHub Pages

Run `bash scripts/docs.sh` to generate the kernel, domain and bridge API documentation.
The separate `docbuild` Lake project pins doc-gen4 to the same Lean release, keeping
documentation tooling out of the library's dependencies. Preview with:

```sh
python3 -m http.server --directory docbuild/.lake/build/api/doc 8000
```

CI builds and verifies the documentation on pull requests. Successful builds on `main`
publish it to [GitHub Pages](https://4137314.github.io/synthesis/) using the official
Pages artifact and deployment actions. Deployment requires successful proof checks.
See [documentation maintenance](docs/documentation.md) for version updates and setup.
