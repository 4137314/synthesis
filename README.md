# synthesis

[API documentation](https://4137314.github.io/synthesis/) · [Source](https://github.com/4137314/synthesis)

A Lean 4 library for engineering descriptions, formal reasoning, and compilation to
a custom multiphysics AST. A small formal kernel supports independently extensible
domain theories. Target backends such as VHDL, GDSII and Python belong downstream.

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
#check Domains.Components.optical_conservation
#check Domains.Chemistry.reachable_elements_conserved
#check Domains.Quantum.Gate.preserves_normalization
#check Bridges.Electrothermal.heater_verified
```

| Domain | Initial model | Proved properties |
| --- | --- | --- |
| Electronics | Ideal passive resistor and series composition | Nonnegative power, voltage/power composition, operating-point existence |
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
- A typed AST with rational SI parameters and checked connections.
- Explicit component/coupling interpretations and non-vacuous requirement certificates.
- Compiler interfaces carrying structural and semantic preservation evidence.

Proofs are kernel-checked. The audit permits only Lean's standard foundational
assumptions (`propext`, `Classical.choice`, `Quot.sound`), with no project-specific
unproved assumptions. Physical laws are explicit model definitions or hypotheses.
The guarantees apply within those models and hypotheses; empirical applicability,
uncertainty, numerical approximation and industrial certification need additional work.

The API is experimental: **0.3.0**, **AST schema 2**. Component parameters are normalized
rational literals; symbolic parameter binding, textual parsing, serialization,
continuous-time solvers and target backends are not implemented. The additional `Domains.RealElectronics` model uses Mathlib real numbers and ring
reasoning. Arbitrary real coefficients are not silently converted to rational AST literals.

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
