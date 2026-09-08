# Contributing

Write code, documentation, comments, diagnostics, issue templates and PR descriptions
in English. Use `Synthesis` for Lean namespaces and `synthesis` for the package.

## Local checks

Enter `nix develop`, then run:

```sh
nixfmt --check flake.nix
bash scripts/cache.sh
bash scripts/check.sh
bash scripts/docs.sh
```

The check script validates the module dependency graph and audit coverage, builds
all default targets, runs executable regressions and audits project declarations.
Lean warnings are errors. New domain modules use `set_option autoImplicit false`
and explicitly declare their universes and variables.

Import reusable foundations through `Synthesis`; import domain models separately
through `Synthesis.Domains` and coupling models through `Synthesis.Bridges`.
Register new modules in the appropriate umbrella and exercise them from a test module.
The audit must transitively import every project module; the checker rejects omissions.

## Model and proof review

Each new model needs an entry in docs/models.md with:

- Scalar and unit conventions, applicability envelope, and authoritative references.
- Its actual constitutive definition and all required hypotheses.
- Named theorems, constructive existence or feasibility evidence, and limitations.
- A parameterized AST component if it is exposed as a compilable primitive.
- Positive nonzero examples and negative cases for invalid assumptions or interfaces.

Physical laws are definitions or explicit hypotheses in a domain model. Do not add
global unproved assumptions to make a theorem pass. Distinguish empirical laws from
logical consequences of those laws. The assumption audit permits only Lean's standard
foundational assumptions: `propext`, `Classical.choice`, and `Quot.sound`.

Changes to accepted AST structures or their interpretation need an ADR and an explicit
schema-version decision. Changes to public imports need migration notes. Update tests,
model documentation and examples together. No backend implementation belongs here.

The lightweight source scanner is a policy check; the Lean kernel and transitive
assumption audit provide proof checking. Review still needs to assess whether the
formal statement corresponds to the intended engineering requirement.

## Agent commit attribution

Agents must not credit themselves as authors or co-authors. Do not add `Co-authored-by`
trailers, agent attribution or AI signatures to commit messages or pull requests.
Use the existing user-configured Git identity. Commit and push only when authorized.

## Dependency and documentation updates

Mathlib is a library dependency; doc-gen4 is isolated in `docbuild`. Keep both compatible
with `lean-toolchain` and commit both Lake manifests. Follow docs/documentation.md when
updating pins. Prefer focused Mathlib imports; do not import all of `Mathlib` merely to
obtain a single theorem or tactic. Generated API output is ignored and deployed by CI.
