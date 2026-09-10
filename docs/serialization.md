# Reference serialization

`IR.Module.encode` produces compact deterministic JSON. `IR.Module.decode` returns
raw canonical IR or structured diagnostics. Decoding is not structural validation,
extension checking, semantic interpretation or proof verification.

The envelope contains `format` (currently 1), `schema` (currently 3), and `module`.
The reference codec explicitly encodes named record fields and tagged alternatives.
The normative contract is [wire format 1](wire-format-v1.md), independent of Lean deriving. Declaration and argument lists retain their order: parameter
scope makes arbitrary sorting unsound. Rational values are normalized numerator /
positive denominator pairs, without floating-point conversion. All canonical module
fields, including attributes, annotations, bindings and provenance, are retained.

Format 1 is pinned by conformance tests. An independently implemented codec must
match those fixtures; changing canonical output requires a new format version,
not silently updating fixtures. Unknown record fields and omitted default fields are
rejected to prevent silent information loss. Unknown extension contracts remain data
and require separate fail-closed extension validation.

The decoder checks a configurable byte budget (default 16 MiB) and a nesting budget (default 256) before parsing.
This is a basic boundary, not a denial-of-service guarantee: large hierarchy expansion and aggregate resource use still need caller limits. Hierarchy traversal has an
explicit depth budget and reports exhaustion. The canonical decoder does not assert
that references resolve or that a hierarchy is acyclic.

Round trips are runtime-tested over generated small recursive IR. There is currently
no kernel theorem about the JSON parser/manual decoder. `Design.Encoding` and
`AttributeCodec` separately require kernel-checked exactness for typed domain data.
ContentDigest provides an explicitly versioned noncryptographic FNV-1a fingerprint of
canonical bytes. RevisionRef keeps logical identity/version distinct from that fingerprint.
It is not authentication or a collision-free content-identity theorem.
