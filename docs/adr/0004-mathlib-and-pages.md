# ADR 0004: Mathlib and generated API publication

Status: accepted. Supersedes the initial dependency-free choice in ADR 0003.
AST schema 2 is unchanged.

Mathlib is an explicit library dependency pinned to its Lean 4.32.2 release commit.
`Domains.RealElectronics` uses its real-number theory and ring normalization to prove
resistor properties beyond rational scalar models. Existing rational models remain
computable; there is no implicit conversion of arbitrary real coefficients into the AST.

Keep runtime frontend regressions separate from real-valued proof modules so the small
test executable does not need to link Mathlib's complete native dependency closure.
Both kinds of tests are built and included in the transitive proof-assumption audit.

Use doc-gen4 in a nested Lake project with its own committed manifest and matching
Lean toolchain. Shared dependency pins must agree with the root project. Documentation
builds must include kernel, domain and bridge API pages and searchable declarations.

GitHub Actions verifies the library before generating and deploying API documentation.
Pull requests can build but cannot publish; main-branch builds deploy using the official
GitHub Pages artifact workflow. Generated documentation is not committed. Agents must
not add authorship/co-authorship trailers or signatures to commits or pull requests.
