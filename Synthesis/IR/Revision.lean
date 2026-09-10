import Synthesis.Core.Revision
import Synthesis.IR.Serialization
import Synthesis.IR.Render

namespace Synthesis.IR
set_option autoImplicit false

/-- Cross-model references always include an explicit revision. Ordinary local queries
continue using EntityRef without repeated revision parameters. -/
structure LocatedEntity where
  revision : RevisionRef
  entity : EntityRef
  deriving Repr, DecidableEq, BEq

/-- Immutable module snapshot. Construction computes the content fingerprint from wire
format 1; no pointer, hash-map iteration or display name contributes to identity. -/
structure ModuleRevision where
  identity : QualifiedId
  version : Symbol
  module : Module
  private digest : ContentDigest
  private digestAgrees : digest = fingerprint module.encode.toUTF8

def ModuleRevision.create (identity : QualifiedId) (version : Symbol) (module : Module) : ModuleRevision :=
  ⟨identity, version, module, fingerprint module.encode.toUTF8, rfl⟩

def ModuleRevision.reference (snapshot : ModuleRevision) : RevisionRef :=
  ⟨snapshot.identity, snapshot.version, some snapshot.digest⟩

def ModuleRevision.locate (snapshot : ModuleRevision) (entity : EntityRef) : LocatedEntity :=
  ⟨snapshot.reference, entity⟩

/-- Reject a stale/cross-revision reference before attempting local lookup. -/
def ModuleRevision.resolve (snapshot : ModuleRevision) (reference : LocatedEntity) :
    Except (List Diagnostic) (ResolvedEntity snapshot.module) :=
  if reference.revision == snapshot.reference then snapshot.module.resolve reference.entity
  else .error [{ (Diagnostic.error "SYN-INTEROP-REVISION-MISMATCH"
    "Entity belongs to a different model revision.") with subject := some reference.entity }]

namespace RevisionWire
open Lean Wire

instance : ToJson ContentDigest where
  toJson digest := object [("scheme", toJson digest.scheme),
    ("bytes", toJson (digest.bytes.map UInt8.toNat))]
instance : FromJson ContentDigest where
  fromJson? json := do
    fields json ["scheme", "bytes"]
    let scheme ← json.getObjValAs? ContractId "scheme"
    let bytes ← json.getObjValAs? (List Nat) "bytes"
    if bytes.any (· > 255) then throw "Digest byte outside 0..255."
    pure ⟨scheme, bytes.map UInt8.ofNat⟩

instance : ToJson RevisionRef where
  toJson revision := object [("identity", toJson revision.identity),
    ("version", toJson revision.version), ("content", toJson revision.content)]
instance : FromJson RevisionRef where
  fromJson? json := do
    fields json ["identity", "version", "content"]
    return ⟨← json.getObjValAs? QualifiedId "identity", ← json.getObjValAs? Symbol "version",
      ← json.getObjValAs? (Option ContentDigest) "content"⟩

instance : ToJson LocatedEntity where
  toJson reference := object [("revision", toJson reference.revision), ("entity", toJson reference.entity)]
instance : FromJson LocatedEntity where
  fromJson? json := do
    fields json ["revision", "entity"]
    return ⟨← json.getObjValAs? RevisionRef "revision", ← json.getObjValAs? EntityRef "entity"⟩

end RevisionWire

/-- Readable revision identity, including the fingerprint scheme when supplied.
This presentation is not a parser input or canonical wire representation. -/
def renderRevision (revision : RevisionRef) : String :=
  s!"{renderId revision.identity}@{revision.version.text}" ++
    (revision.content.map (fun digest =>
      s!" [{renderContract digest.scheme}:{digest.hex}]") |>.getD "")

/-- Deterministic diagnostic rendering, separate from canonical wire representation. -/
def LocatedEntity.render (reference : LocatedEntity) : String :=
  s!"{renderRevision reference.revision}: {reference.entity.render}"

end Synthesis.IR
