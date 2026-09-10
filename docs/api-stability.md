# API stability policy

Synthesis is a Lean source library, not a binary ABI. Stable semantics matter more
than record layout. During 0.x, breaking changes require release notes and migration
instructions. This policy establishes the supported boundary; it is not a claim of
industrial qualification or a promise that every 0.x declaration is frozen.

Supported conceptual APIs are identity, canonical schema, logical query, validation
staging, interpretation, contracts, refinement, explicit extension ownership,
information prerequisites and proof-producing translation validation. Public entry
points are `Synthesis`, `Synthesis.IR`, `Synthesis.Design`, `Synthesis.Semantics`,
`Synthesis.Frontend` and `Synthesis.Interop`. Domain packages are separate imports.

Experimental APIs include embedded syntax, builder implementation types, source-map
editor conventions and the reference serialization implementation. Their documented
behavior is tested, but ergonomic changes may occur in a minor release. Recursive
storage helpers, private declarations and derived index fields are implementation
only. Raw IR constructors remain available for importers and malformed-input tests;
ordinary consumers should use queries rather than assume storage containers.

A change to the meaning of `Refines`, `Validated`, `Checked`, `Verified` or contract
satisfaction is a semantic compatibility event even with unchanged signatures. Such
changes require an ADR and a breaking release. A storage optimization must preserve
query order, resolution and validation results or explicitly change the contract.

When deprecation is needed, document the replacement, first deprecated release and
planned removal release. Normally allow one minor release of migration time in 0.x;
trust-boundary defects may require immediate removal with an explanation. Do not
maintain indefinite parallel architectures.

IR schema, library API, serialization format and interop protocol versions are
independent. Changing a codec cannot reinterpret an old wire version. Unknown data
within an existing extension payload is retained as Data; unknown envelope/record
fields are rejected. Upgrades use explicit migrations with information disclosures.


Compatibility dimensions are independent: source signatures, mathematical semantics,
canonical schema fields, wire bytes, diagnostic codes, trace revision boundaries and
migration preconditions. A change in one requires naming that dimension, its reason,
replacement API and version decision. Stable semantics take precedence over unchanged
function signatures. Protocol 2 in API 0.6.1 is an explicit breaking trace-safety repair;
there is no implicit conversion of protocol-1 local-only traces into trusted revisioned
traces. See ADR 0009 and the pre-1.0 technical criteria.
