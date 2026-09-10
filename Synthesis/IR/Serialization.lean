import Lean
import Std.Data.HashSet.Basic
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

-- Format-1 object layout is explicit. Primitive JSON parsing is shared, but no
-- public record or sum layout is derived from Lean declarations.
namespace Wire

def object (fields : List (String × Json)) : Json := Json.mkObj fields

def fields (json : Json) (expected : List String) : Except String Unit := do
  let obj ← json.getObj?
  if obj.toList.map (·.1) != expected.mergeSort (· ≤ ·) then
    throw "Missing or unknown wire fields."

instance : ToJson Symbol where
  toJson value := object [
    ("text", toJson value.text)]

instance : FromJson Symbol where
  fromJson? json := do
    fields json ["text"]
    let f0 ← json.getObjValAs? String "text"
    pure ⟨f0⟩

instance : ToJson QualifiedId where
  toJson value := object [
    ("segments", toJson value.segments)]

instance : FromJson QualifiedId where
  fromJson? json := do
    fields json ["segments"]
    let f0 ← json.getObjValAs? (List String) "segments"
    pure ⟨f0⟩

instance : ToJson ContractId where
  toJson value := object [
    ("name", toJson value.name),
    ("version", toJson value.version)]

instance : FromJson ContractId where
  fromJson? json := do
    fields json ["name", "version"]
    let f0 ← json.getObjValAs? QualifiedId "name"
    let f1 ← json.getObjValAs? Nat "version"
    pure ⟨f0, f1⟩

mutual
  def encodeData : Data → Json
    | .rational x0 => object [("rational", object [("value", toJson x0)])]
    | .integer x0 => object [("integer", object [("value", toJson x0)])]
    | .text x0 => object [("text", object [("value", toJson x0)])]
    | .symbol x0 => object [("symbol", object [("value", toJson x0)])]
    | .sequence x0 => object [("sequence", object [("values", Json.arr ((encodeDataList x0).toArray))])]
    | .tagged x0 x1 => object [("tagged", object [("contract", toJson x0), ("values", Json.arr ((encodeDataList x1).toArray))])]
    termination_by structural value => value

  def encodeDataList : List Data → List Json
    | [] => []
    | value :: rest => encodeData value :: encodeDataList rest
    termination_by structural values => values
end

instance : ToJson Data := ⟨encodeData⟩

def decodeData : Nat → Json → Except String Data
  | 0, _ => .error "Wire recursion limit exceeded."
  | fuel + 1, json => do
    let obj ← json.getObj?
    match obj.toList with
    | [("rational", body)] => do
      fields body ["value"]
      let x0 ← body.getObjValAs? Rat "value"
      pure (.rational x0)
    | [("integer", body)] => do
      fields body ["value"]
      let x0 ← body.getObjValAs? Int "value"
      pure (.integer x0)
    | [("text", body)] => do
      fields body ["value"]
      let x0 ← body.getObjValAs? String "value"
      pure (.text x0)
    | [("symbol", body)] => do
      fields body ["value"]
      let x0 ← body.getObjValAs? Symbol "value"
      pure (.symbol x0)
    | [("sequence", body)] => do
      fields body ["values"]
      let raw ← body.getObjValAs? (Array Json) "values"
      let x0 ← raw.toList.mapM (decodeData fuel)
      pure (.sequence x0)
    | [("tagged", body)] => do
      fields body ["contract", "values"]
      let x0 ← body.getObjValAs? ContractId "contract"
      let raw ← body.getObjValAs? (Array Json) "values"
      let x1 ← raw.toList.mapM (decodeData fuel)
      pure (.tagged x0 x1)
    | _ => throw "Unknown or malformed sum tag."

instance : FromJson Data := ⟨decodeData 256⟩

instance : ToJson TypeExpr where
  toJson value := object [
    ("constructor", toJson value.constructor),
    ("arguments", toJson value.arguments)]

instance : FromJson TypeExpr where
  fromJson? json := do
    fields json ["constructor", "arguments"]
    let f0 ← json.getObjValAs? ContractId "constructor"
    let f1 ← json.getObjValAs? (List Data) "arguments"
    pure ⟨f0, f1⟩

mutual
  def encodeTerm : Term → Json
    | .literal x0 x1 => object [("literal", object [("type", toJson x0), ("value", toJson x1)])]
    | .variable x0 => object [("variable", object [("name", toJson x0)])]
    | .apply x0 x1 => object [("apply", object [("operation", toJson x0), ("arguments", Json.arr ((encodeTermList x1).toArray))])]
    termination_by structural value => value

  def encodeTermList : List Term → List Json
    | [] => []
    | value :: rest => encodeTerm value :: encodeTermList rest
    termination_by structural values => values
end

instance : ToJson Term := ⟨encodeTerm⟩

def decodeTerm : Nat → Json → Except String Term
  | 0, _ => .error "Wire recursion limit exceeded."
  | fuel + 1, json => do
    let obj ← json.getObj?
    match obj.toList with
    | [("literal", body)] => do
      fields body ["type", "value"]
      let x0 ← body.getObjValAs? TypeExpr "type"
      let x1 ← body.getObjValAs? Data "value"
      pure (.literal x0 x1)
    | [("variable", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.variable x0)
    | [("apply", body)] => do
      fields body ["operation", "arguments"]
      let x0 ← body.getObjValAs? ContractId "operation"
      let raw ← body.getObjValAs? (Array Json) "arguments"
      let x1 ← raw.toList.mapM (decodeTerm fuel)
      pure (.apply x0 x1)
    | _ => throw "Unknown or malformed sum tag."

instance : FromJson Term := ⟨decodeTerm 256⟩

instance : ToJson Binding where
  toJson value := object [
    ("name", toJson value.name),
    ("value", toJson value.value)]

instance : FromJson Binding where
  fromJson? json := do
    fields json ["name", "value"]
    let f0 ← json.getObjValAs? Symbol "name"
    let f1 ← json.getObjValAs? Term "value"
    pure ⟨f0, f1⟩

instance : ToJson Parameter where
  toJson value := object [
    ("name", toJson value.name),
    ("type", toJson value.type),
    ("value", toJson value.value)]

instance : FromJson Parameter where
  fromJson? json := do
    fields json ["name", "type", "value"]
    let f0 ← json.getObjValAs? Symbol "name"
    let f1 ← json.getObjValAs? TypeExpr "type"
    let f2 ← json.getObjValAs? (Option Term) "value"
    pure ⟨f0, f1, f2⟩

instance : ToJson Attribute where
  toJson value := object [
    ("contract", toJson value.contract),
    ("value", toJson value.value)]

instance : FromJson Attribute where
  fromJson? json := do
    fields json ["contract", "value"]
    let f0 ← json.getObjValAs? ContractId "contract"
    let f1 ← json.getObjValAs? Data "value"
    pure ⟨f0, f1⟩

instance : ToJson SourceSpan where
  toJson value := object [
    ("source", toJson value.source),
    ("start", toJson value.start),
    ("stop", toJson value.stop)]

instance : FromJson SourceSpan where
  fromJson? json := do
    fields json ["source", "start", "stop"]
    let f0 ← json.getObjValAs? String "source"
    let f1 ← json.getObjValAs? Nat "start"
    let f2 ← json.getObjValAs? Nat "stop"
    pure ⟨f0, f1, f2⟩

instance : ToJson Provenance where
  toJson value := object [
    ("source", toJson value.source),
    ("origin", toJson value.origin),
    ("parents", toJson value.parents),
    ("transformation", toJson value.transformation)]

instance : FromJson Provenance where
  fromJson? json := do
    fields json ["source", "origin", "parents", "transformation"]
    let f0 ← json.getObjValAs? (Option SourceSpan) "source"
    let f1 ← json.getObjValAs? (Option QualifiedId) "origin"
    let f2 ← json.getObjValAs? (List QualifiedId) "parents"
    let f3 ← json.getObjValAs? (Option ContractId) "transformation"
    pure ⟨f0, f1, f2, f3⟩

instance : ToJson Annotation where
  toJson value := object [
    ("key", toJson value.key),
    ("value", toJson value.value)]

instance : FromJson Annotation where
  fromJson? json := do
    fields json ["key", "value"]
    let f0 ← json.getObjValAs? QualifiedId "key"
    let f1 ← json.getObjValAs? Data "value"
    pure ⟨f0, f1⟩

instance : ToJson Port where
  toJson value := object [
    ("name", toJson value.name),
    ("interface", toJson value.interface),
    ("type", toJson value.type),
    ("role", toJson value.role),
    ("attributes", toJson value.attributes)]

instance : FromJson Port where
  fromJson? json := do
    fields json ["name", "interface", "type", "role", "attributes"]
    let f0 ← json.getObjValAs? Symbol "name"
    let f1 ← json.getObjValAs? ContractId "interface"
    let f2 ← json.getObjValAs? TypeExpr "type"
    let f3 ← json.getObjValAs? ContractId "role"
    let f4 ← json.getObjValAs? (List Attribute) "attributes"
    pure ⟨f0, f1, f2, f3, f4⟩

instance : ToJson Endpoint where
  toJson value := object [
    ("path", toJson value.path),
    ("port", toJson value.port)]

instance : FromJson Endpoint where
  fromJson? json := do
    fields json ["path", "port"]
    let f0 ← json.getObjValAs? (List Symbol) "path"
    let f1 ← json.getObjValAs? Symbol "port"
    pure ⟨f0, f1⟩

instance : ToJson Junction where
  toJson value := object [
    ("name", toJson value.name),
    ("contract", toJson value.contract),
    ("endpoints", toJson value.endpoints),
    ("attributes", toJson value.attributes),
    ("provenance", toJson value.provenance)]

instance : FromJson Junction where
  fromJson? json := do
    fields json ["name", "contract", "endpoints", "attributes", "provenance"]
    let f0 ← json.getObjValAs? Symbol "name"
    let f1 ← json.getObjValAs? ContractId "contract"
    let f2 ← json.getObjValAs? (List Endpoint) "endpoints"
    let f3 ← json.getObjValAs? (List Attribute) "attributes"
    let f4 ← json.getObjValAs? Provenance "provenance"
    pure ⟨f0, f1, f2, f3, f4⟩

mutual
  def encodeOperation : Operation → Json
    | .node x0 x1 x2 x3 x4 x5 x6 => object [("node", object [("name", toJson x0), ("contract", toJson x1), ("arguments", toJson x2), ("results", toJson x3), ("attributes", toJson x4), ("body", Json.arr ((encodeOperationList x5).toArray)), ("provenance", toJson x6)])]
    termination_by structural value => value

  def encodeOperationList : List Operation → List Json
    | [] => []
    | value :: rest => encodeOperation value :: encodeOperationList rest
    termination_by structural values => values
end

instance : ToJson Operation := ⟨encodeOperation⟩

def decodeOperation : Nat → Json → Except String Operation
  | 0, _ => .error "Wire recursion limit exceeded."
  | fuel + 1, json => do
    let obj ← json.getObj?
    match obj.toList with
    | [("node", body)] => do
      fields body ["name", "contract", "arguments", "results", "attributes", "body", "provenance"]
      let x0 ← body.getObjValAs? Symbol "name"
      let x1 ← body.getObjValAs? ContractId "contract"
      let x2 ← body.getObjValAs? (List Term) "arguments"
      let x3 ← body.getObjValAs? (List Parameter) "results"
      let x4 ← body.getObjValAs? (List Attribute) "attributes"
      let raw ← body.getObjValAs? (Array Json) "body"
      let x5 ← raw.toList.mapM (decodeOperation fuel)
      let x6 ← body.getObjValAs? Provenance "provenance"
      pure (.node x0 x1 x2 x3 x4 x5 x6)
    | _ => throw "Unknown or malformed sum tag."

instance : FromJson Operation := ⟨decodeOperation 256⟩

instance : ToJson Instance where
  toJson value := object [
    ("name", toJson value.name),
    ("definition", toJson value.definition),
    ("bindings", toJson value.bindings),
    ("attributes", toJson value.attributes),
    ("provenance", toJson value.provenance)]

instance : FromJson Instance where
  fromJson? json := do
    fields json ["name", "definition", "bindings", "attributes", "provenance"]
    let f0 ← json.getObjValAs? Symbol "name"
    let f1 ← json.getObjValAs? QualifiedId "definition"
    let f2 ← json.getObjValAs? (List Binding) "bindings"
    let f3 ← json.getObjValAs? (List Attribute) "attributes"
    let f4 ← json.getObjValAs? Provenance "provenance"
    pure ⟨f0, f1, f2, f3, f4⟩

instance : ToJson Definition where
  toJson value := object [
    ("id", toJson value.id),
    ("parameters", toJson value.parameters),
    ("ports", toJson value.ports),
    ("instances", toJson value.instances),
    ("junctions", toJson value.junctions),
    ("operations", toJson value.operations),
    ("attributes", toJson value.attributes),
    ("annotations", toJson value.annotations),
    ("provenance", toJson value.provenance)]

instance : FromJson Definition where
  fromJson? json := do
    fields json ["id", "parameters", "ports", "instances", "junctions", "operations", "attributes", "annotations", "provenance"]
    let f0 ← json.getObjValAs? QualifiedId "id"
    let f1 ← json.getObjValAs? (List Parameter) "parameters"
    let f2 ← json.getObjValAs? (List Port) "ports"
    let f3 ← json.getObjValAs? (List Instance) "instances"
    let f4 ← json.getObjValAs? (List Junction) "junctions"
    let f5 ← json.getObjValAs? (List Operation) "operations"
    let f6 ← json.getObjValAs? (List Attribute) "attributes"
    let f7 ← json.getObjValAs? (List Annotation) "annotations"
    let f8 ← json.getObjValAs? Provenance "provenance"
    pure ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩

instance : ToJson Module where
  toJson value := object [
    ("definitions", toJson value.definitions),
    ("root", toJson value.root),
    ("bindings", toJson value.bindings),
    ("attributes", toJson value.attributes),
    ("annotations", toJson value.annotations),
    ("provenance", toJson value.provenance),
    ("schema", toJson value.schema)]

instance : FromJson Module where
  fromJson? json := do
    fields json ["definitions", "root", "bindings", "attributes", "annotations", "provenance", "schema"]
    let f0 ← json.getObjValAs? (List Definition) "definitions"
    let f1 ← json.getObjValAs? QualifiedId "root"
    let f2 ← json.getObjValAs? (List Binding) "bindings"
    let f3 ← json.getObjValAs? (List Attribute) "attributes"
    let f4 ← json.getObjValAs? (List Annotation) "annotations"
    let f5 ← json.getObjValAs? Provenance "provenance"
    let f6 ← json.getObjValAs? Nat "schema"
    pure ⟨f0, f1, f2, f3, f4, f5, f6⟩

def encodeEntityStep : EntityStep → Json
  | .parameter x0 => object [("parameter", object [("name", toJson x0)])]
  | .port x0 => object [("port", object [("name", toJson x0)])]
  | .instance x0 => object [("instance", object [("name", toJson x0)])]
  | .junction x0 => object [("junction", object [("name", toJson x0)])]
  | .operation x0 => object [("operation", object [("name", toJson x0)])]
  | .result x0 => object [("result", object [("name", toJson x0)])]
  | .binding x0 => object [("binding", object [("name", toJson x0)])]
  | .argument x0 => object [("argument", object [("position", toJson x0)])]
  | .attribute x0 x1 => object [("attribute", object [("contract", toJson x0), ("occurrence", toJson x1)])]

instance : ToJson EntityStep := ⟨encodeEntityStep⟩

def decodeEntityStep : Nat → Json → Except String EntityStep
  | 0, _ => .error "Wire recursion limit exceeded."
  | _fuel + 1, json => do
    let obj ← json.getObj?
    match obj.toList with
    | [("parameter", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.parameter x0)
    | [("port", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.port x0)
    | [("instance", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.instance x0)
    | [("junction", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.junction x0)
    | [("operation", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.operation x0)
    | [("result", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.result x0)
    | [("binding", body)] => do
      fields body ["name"]
      let x0 ← body.getObjValAs? Symbol "name"
      pure (.binding x0)
    | [("argument", body)] => do
      fields body ["position"]
      let x0 ← body.getObjValAs? Nat "position"
      pure (.argument x0)
    | [("attribute", body)] => do
      fields body ["contract", "occurrence"]
      let x0 ← body.getObjValAs? ContractId "contract"
      let x1 ← body.getObjValAs? Nat "occurrence"
      pure (.attribute x0 x1)
    | _ => throw "Unknown or malformed sum tag."

instance : FromJson EntityStep := ⟨decodeEntityStep 256⟩

instance : ToJson EntityRef where
  toJson value := object [
    ("definition", toJson value.definition),
    ("instances", toJson value.instances),
    ("steps", toJson value.steps)]

instance : FromJson EntityRef where
  fromJson? json := do
    fields json ["definition", "instances", "steps"]
    let f0 ← json.getObjValAs? (Option QualifiedId) "definition"
    let f1 ← json.getObjValAs? (List Symbol) "instances"
    let f2 ← json.getObjValAs? (List EntityStep) "steps"
    pure ⟨f0, f1, f2⟩

end Wire

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

/-- Reject duplicate object keys before the JSON parser can coalesce them. Keys are
unescaped with the JSON string parser, so escaped aliases are duplicates too. -/
private def uniqueKeys (text : String) : Bool := Id.run do
  let mut scopes : List (Std.HashSet String) := []
  let mut quoted := false
  let mut escaped := false
  let mut buffer : List Char := []
  let mut pending : Option String := none
  for c in text do
    if quoted then
      buffer := c :: buffer
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then
        quoted := false
        pending := some (String.ofList buffer.reverse)
    else if c == '"' then
      quoted := true
      buffer := ['"']
    else if c == '{' || c == '[' then
      scopes := ∅ :: scopes
      pending := none
    else if c == '}' || c == ']' then
      scopes := scopes.drop 1
      pending := none
    else if c == ':' then
      match pending, scopes with
      | some raw, keys :: rest =>
        match Json.parse raw with
        | .ok (.str key) =>
          if keys.contains key then return false
          scopes := keys.insert key :: rest
        | _ => pure ()
      | _, _ => pure ()
      pending := none
    else if !c.isWhitespace then pending := none
  return true

/-- Shared bounded protocol parser. It checks duplicate keys before coalescing JSON
objects. Domain/wire decoders must still validate their explicit field schemas. -/
def Wire.parse (text : String) (maxBytes : Nat := 16777216) (maxDepth : Nat := 256) :
    Except (List Diagnostic) Json :=
  if text.utf8ByteSize > maxBytes || !withinNesting text maxDepth then
    .error [Diagnostic.error "SYN-IR-DECODE-LIMIT" "Serialized input exceeds the configured byte or nesting budget."]
  else if !uniqueKeys text then
    .error [Diagnostic.error "SYN-IR-DUPLICATE-FIELD" "Duplicate JSON object key."]
  else match Json.parse text with
    | .error message => .error [Diagnostic.error "SYN-IR-DECODE" message]
    | .ok json => .ok json

/-- Decoding preserves raw IR, not structural or semantic assurance. Run validation
and extension checking independently. Input length is bounded before JSON parsing. -/
def Module.decode (text : String) (maxBytes : Nat := 16777216)
    (maxDepth : Nat := 256) : Except (List Diagnostic) Module :=
  match Wire.parse text maxBytes maxDepth with
    | .error errors => .error errors
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
