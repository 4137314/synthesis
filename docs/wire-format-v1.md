# Synthesis IR Wire Format 1

This document specifies format 1 for canonical IR schema 3. It is normative for
independent implementations; no Lean deriving convention is part of this contract.
Examples and acceptance/rejection vectors are in `Tests/Conformance/Wire/v1`.

## JSON and canonical bytes

Encoding is UTF-8 JSON without a BOM, indentation, optional whitespace or final newline.
Object keys are sorted lexicographically by Unicode scalar values. All protocol keys
below are ASCII. Arrays retain their declared order. Every listed record field is
required, including empty arrays and null optionals. No fields may be added or omitted.

Canonical integers use decimal digits, no leading zero except `0`, and a minus sign
only for negative values. There is no size limit implied by IEEE-754: implementations
must use arbitrary precision or reject unsupported magnitudes, never round. All numeric
fields below are integers. Nonnegative fields reject negative numbers. JSON numeric
syntax accepted by a decoder must denote an exact integer; re-encoding uses the integer
form. NaN and infinity are invalid JSON and are not accepted.

Strings retain Unicode scalar values without normalization. Escape quote as `\"`,
backslash as `\\`, LF as `\n`, CR as `\r`; escape every other scalar below U+0020 as
`\u00xx` with lowercase hex. Other scalars appear as UTF-8. In particular TAB is
`\u0009`, not `\t`, in canonical output. Do not escape `/` or non-ASCII scalars.
Decoders accept equivalent JSON string escapes and insignificant whitespace/key order.

Duplicate keys are rejected, including aliases using escapes such as `format` and
`fo\u0072mat`. Unknown/missing fields and unknown sum tags are rejected. Unknown
engineering contracts inside defined open data fields are preserved; decoding does
not interpret or accept their engineering semantics.

## Notation

`T[]` means an ordered JSON array. `T?` means either `null` or the encoding of T.
A sum is an object with exactly one key, its tag; its value is the payload record.
`N` is a nonnegative integer, `Z` an integer, and `S` a string. Empty containers are
`[]`, never omitted. An optional object is `null`, never `{}`.

## Identity and primitive data

| Type | Exact fields/representation |
| --- | --- |
| Symbol | `{ "text": S }` |
| QualifiedId | `{ "segments": S[] }` |
| ContractId | `{ "name": QualifiedId, "version": N }` |
| Rational | `[Z, N]`, denominator positive, numerator/denominator coprime |
| TypeExpr | `{ "constructor": ContractId, "arguments": Data[] }` |

Rational zero is `[0,1]`. Negative denominators, denominator zero and nonreduced pairs
are rejected. Identity validity (nonempty segments, positive contract version, unique
names) is a separate structural/extension check: the wire preserves raw declarations.
Qualified IDs are segmented; a dot inside one segment is not a namespace separator.

Data tags and their exact payload fields:

| Tag | Payload |
| --- | --- |
| rational | `{ "value": Rational }` |
| integer | `{ "value": Z }` |
| text | `{ "value": S }` |
| symbol | `{ "value": Symbol }` |
| sequence | `{ "values": Data[] }` |
| tagged | `{ "contract": ContractId, "values": Data[] }` |

For example, integer data is `{"integer":{"value":42}}`, not the JSON number 42.

## Expressions and provenance

| Term tag | Exact payload |
| --- | --- |
| literal | `{ "type": TypeExpr, "value": Data }` |
| variable | `{ "name": Symbol }` |
| apply | `{ "operation": ContractId, "arguments": Term[] }` |

| Record | Exact fields |
| --- | --- |
| Binding | name: Symbol; value: Term |
| Parameter | name: Symbol; type: TypeExpr; value: Term? |
| Attribute | contract: ContractId; value: Data |
| Annotation | key: QualifiedId; value: Data |
| SourceSpan | source: S; start: N; stop: N |
| Provenance | source: SourceSpan?; origin: QualifiedId?; parents: QualifiedId[]; transformation: ContractId? |

Source spans are UTF-8 byte offsets, start inclusive and stop exclusive. They identify
source text, not engineering entity identity. Legacy schema-3 origin/parents are coarse
qualified origin IDs; precise cross-model relationships use protocol-2 revision traces.

## Engineering structure

| Record | Exact fields |
| --- | --- |
| Port | name: Symbol; interface: ContractId; type: TypeExpr; role: ContractId; attributes: Attribute[] |
| Endpoint | path: Symbol[]; port: Symbol |
| Junction | name: Symbol; contract: ContractId; endpoints: Endpoint[]; attributes: Attribute[]; provenance: Provenance |
| Instance | name: Symbol; definition: QualifiedId; bindings: Binding[]; attributes: Attribute[]; provenance: Provenance |
| Definition | id: QualifiedId; parameters: Parameter[]; ports: Port[]; instances: Instance[]; junctions: Junction[]; operations: Operation[]; attributes: Attribute[]; annotations: Annotation[]; provenance: Provenance |
| Module | definitions: Definition[]; root: QualifiedId; bindings: Binding[]; attributes: Attribute[]; annotations: Annotation[]; provenance: Provenance; schema: N |

Operation is the single-tag sum `{"node": payload}`. Its payload has exactly:
name: Symbol; contract: ContractId; arguments: Term[]; results: Parameter[];
attributes: Attribute[]; body: Operation[]; provenance: Provenance.

The module envelope has exactly `format: 1`, `schema: 3`, `module: Module`.
Module.schema must equal the envelope schema. Unsupported versions are rejected, not
reinterpreted. A future migration first decodes its actual source format/schema.

Declaration ordering is structural identity. The encoder never sorts definitions,
parameters, ports, attributes or operations. It performs no engineering rewriting,
constant folding, default filling, causalization or specialization. Byte identity
means structural wire identity, not semantic equivalence.

## Local and revision-qualified references

EntityRef fields: `definition: QualifiedId?`, `instances: Symbol[]`, `steps: EntityStep[]`.
A null definition with an empty instance path addresses the module; otherwise a null
definition selects the root before following instance occurrences.

EntityStep tags parameter, port, instance, junction, operation, result and binding
have payload `{ "name": Symbol }`. Argument has `{ "position": N }`. Attribute has
`{ "contract": ContractId, "occurrence": N }`. Positions are zero-based and change
when the corresponding argument/attribute sequence is reordered. Named steps do not.

Revision metadata belongs to interop protocol 2, not the module envelope:

| Record | Exact fields |
| --- | --- |
| ContentDigest | scheme: ContractId; bytes: N[] (each 0..255) |
| RevisionRef | identity: QualifiedId; version: Symbol; content: ContentDigest? |
| LocatedEntity | revision: RevisionRef; entity: EntityRef |

Owners must not reuse an identity/version pair for different content. Digest equality
is neither authentication nor a proof of semantic equality. ModuleRevision caches the
fingerprint with a correspondence proof; ordinary local queries do not recompute it.

## Fingerprint scheme 1

The provided scheme ContractId has name segments
`["synthesis.fingerprint", "fnv1a64-be"]` and version 1. Start at unsigned
14695981039346656037. For each canonical UTF-8 byte b, replace h by
`((h XOR b) * 1099511628211) mod 2^64`. Output eight bytes, most significant first.
Manifest digest strings are lowercase hex of those bytes. No trailing file newline
is hashed. This is **noncryptographic change detection**. It must not be used alone
for adversarial content addressing, signatures or security decisions. Other schemes
can use their own contract IDs without changing schema 3.

## Diagnostics and limits

Stable decoder codes: SYN-IR-DECODE (invalid syntax/field/value),
SYN-IR-DUPLICATE-FIELD, SYN-IR-DECODE-LIMIT, SYN-IR-UNSUPPORTED-VERSION, and
SYN-IR-DECODE-NONCANONICAL (envelope/representation inconsistency).
The reference decoder defaults to 16 MiB and JSON nesting depth 256. Individual
recursive Data/Term/Operation decoders also bound recursion to 256. Raising the parser
budget does not remove those decoder bounds. Limits are implementation resource
policy; callers must handle rejection explicitly.

Fixtures specify accept/reject, canonical re-encoding, versions, fingerprint scheme
and expected stable rejection code. Round trips and byte compatibility are tested.
There is no theorem asserting correctness of the JSON parser or the entire codec.
