import Lean
import Synthesis.IR.Diagnostic

namespace Synthesis.IR
set_option autoImplicit false
open Lean

/-- A format-independent codec boundary. A lawful codec can separately carry an
exactness proof; a tested reference implementation must not claim one implicitly. -/
structure Codec (Value Wire : Type) where
  encode : Value → Wire
  decode : Wire → Except (List Diagnostic) Value

def Codec.Exact {Value Wire : Type} (codec : Codec Value Wire) : Prop :=
  ∀ value, codec.decode (codec.encode value) = .ok value

/-- Reference encoding version; independent from the logical IR schema. -/
def serializationVersion : Nat := 1

instance : ToJson Rat where
  toJson r := toJson (r.num, r.den)
instance : FromJson Rat where
  fromJson? json := do
    let (num, den) ← (fromJson? json : Except String (Int × Nat))
    if h : den = 0 then throw "Rational denominator must be positive."
    else
      let value := Rat.normalize num den h
      if value.num != num || value.den != den then
        throw "Rational must be in normalized form."
      pure value

deriving instance ToJson, FromJson for Symbol, QualifiedId, ContractId
deriving instance ToJson, FromJson for EntityStep, EntityRef
deriving instance ToJson, FromJson for Data
deriving instance ToJson, FromJson for TypeExpr
deriving instance ToJson, FromJson for Term
deriving instance ToJson, FromJson for Binding, Parameter, Attribute, SourceSpan, Provenance, Annotation
deriving instance ToJson, FromJson for Port, Endpoint, Junction
deriving instance ToJson, FromJson for Operation
deriving instance ToJson, FromJson for Instance, Definition, Module

/-- Encoding preserves declaration order. It does not reorder scopes or claim semantic
normalization. Lean's deterministic compact JSON writer is the reference text format. -/
def Module.encode (m : Module) : String :=
  (Json.mkObj [("format", toJson serializationVersion), ("schema", toJson m.schema),
    ("module", toJson m)]).compress

/-- Preflight JSON nesting before invoking the parser. Quoted/escaped braces do not
consume depth. Malformed syntax is still the parser's responsibility. -/
private def withinNesting (text : String) (limit : Nat) : Bool :=
  let (_, _, _, valid) := text.foldl (fun (depth, quoted, escaped, valid) c =>
    if quoted then
      if escaped then (depth, true, false, valid)
      else if c == '\\' then (depth, true, true, valid)
      else if c == '"' then (depth, false, false, valid)
      else (depth, true, false, valid)
    else if c == '"' then (depth, true, false, valid)
    else if c == '{' || c == '[' then (depth + 1, false, false, valid && depth < limit)
    else if c == '}' || c == ']' then (depth - 1, false, false, valid)
    else (depth, false, false, valid)) (0, false, false, true)
  valid

/-- Decoding preserves raw IR, not structural or semantic assurance. Run validation
and extension checking independently. Input length is bounded before JSON parsing. -/
def Module.decode (text : String) (maxBytes : Nat := 16777216)
    (maxDepth : Nat := 256) : Except (List Diagnostic) Module :=
  if text.utf8ByteSize > maxBytes || !withinNesting text maxDepth then
    .error [Diagnostic.error "SYN-IR-DECODE-LIMIT" "Serialized input exceeds the configured byte or nesting budget."]
  else
    match Json.parse text with
    | .error message => .error [Diagnostic.error "SYN-IR-DECODE" message]
    | .ok json =>
      match (do
        let format ← json.getObjValAs? Nat "format"
        let schema ← json.getObjValAs? Nat "schema"
        pure (format, schema) : Except String (Nat × Nat)) with
      | .error message => .error [Diagnostic.error "SYN-IR-DECODE" message]
      | .ok (format, schema) =>
        if format != serializationVersion || schema != schemaVersion then
          .error [Diagnostic.error "SYN-IR-UNSUPPORTED-VERSION" "Unsupported serialization format or IR schema version."]
        else match json.getObjValAs? Module "module" with
          | .error message => .error [Diagnostic.error "SYN-IR-DECODE" message]
          | .ok m => if m.schema != schema then
              .error [Diagnostic.error "SYN-IR-UNSUPPORTED-VERSION" "Envelope and module schema versions disagree."]
            else if json != Json.mkObj [("format", toJson serializationVersion),
                ("schema", toJson m.schema), ("module", toJson m)] then
              .error [Diagnostic.error "SYN-IR-DECODE-NONCANONICAL"
                "Unknown fields, omitted fields or noncanonical values require an explicit migration."]
            else .ok m

end Synthesis.IR
