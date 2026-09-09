import Synthesis.IR.Query

namespace Synthesis.Frontend
set_option autoImplicit false

/-- A scoped reference is tied to an immutable snapshot and the requested entity
predicate. A handle cannot be reused as evidence for an edited module. -/
structure Reference (m : IR.Module) (kind : IR.Entity → Prop) extends IR.ResolvedEntity m where
  hasKind : kind entity

/-- Domain frontends choose their own entity predicates; no domain registry is needed. -/
def resolveReference (m : IR.Module) (kind : IR.Entity → Prop) [DecidablePred kind]
    (reference : IR.EntityRef) : Except (List IR.Diagnostic) (Reference m kind) := do
  let resolved ← m.resolve reference
  if h : kind resolved.entity then pure ⟨resolved, h⟩
  else throw [{ (IR.Diagnostic.error "SYN-FRONTEND-REFERENCE-KIND"
    "Resolved entity does not have the expected kind.") with subject := some reference }]

/-- Portable offset locations and editor line/column coordinates are separate views.
Offsets and columns are UTF-8 bytes, lines and columns are zero-based. -/
structure SourcePosition where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq

/-- A source map owns text separately from portable IR. -/
structure SourceDocument where
  id : String
  text : String

def SourceDocument.position (doc : SourceDocument) (offset : Nat) : Option SourcePosition :=
  if offset > doc.text.utf8ByteSize then none
  else
    let bytes := doc.text.toUTF8.toList.take offset
    some (bytes.foldl (fun pos byte =>
      if byte == 10 then ⟨pos.line + 1, 0⟩ else ⟨pos.line, pos.column + 1⟩) ⟨0, 0⟩)

/-- Source navigation needs no frontend parser state. Invalid/reversed spans fail. -/
def SourceDocument.range (doc : SourceDocument) (span : IR.SourceSpan) :
    Option (SourcePosition × SourcePosition) := do
  if span.source != doc.id || span.start > span.stop then none else pure ()
  let start ← doc.position span.start
  let stop ← doc.position span.stop
  pure (start, stop)

/-- Fine-grained frontend provenance can accompany canonical IR without requiring a
source field on every schema record. These entries are data, not parser state. -/
structure SourceBinding where
  entity : IR.EntityRef
  span : IR.SourceSpan
  deriving Repr, DecidableEq

structure SourceMap where
  entries : List SourceBinding := []
  deriving Repr, DecidableEq

def SourceMap.find (map : SourceMap) (entity : IR.EntityRef) : List IR.SourceSpan :=
  map.entries.filterMap (fun entry => if entry.entity == entity then some entry.span else none)

def SourceMap.atPosition (map : SourceMap) (file : String) (offset : Nat) : List IR.EntityRef :=
  map.entries.filterMap fun entry =>
    if entry.span.source == file && entry.span.start ≤ offset && offset < entry.span.stop then
      some entry.entity else none

end Synthesis.Frontend
