import Synthesis.Frontend.Scope
import Synthesis.IR.Revision

namespace Synthesis.Frontend
set_option autoImplicit false

/-- Revision context belongs to the source-map envelope, not every intra-module query. -/
structure RevisionSourceMap where
  revision : RevisionRef
  map : SourceMap

/-- Generated helpers retain explicit source-parent lineage without changing schema 3. -/
structure GeneratedOrigin where
  entity : IR.LocatedEntity
  parents : List IR.LocatedEntity
  construct : ContractId
  source : Option IR.SourceSpan := none

def RevisionSourceMap.entityAtPosition (sourceMap : RevisionSourceMap) (file : String) (offset : Nat) :
    List IR.LocatedEntity :=
  (sourceMap.map.atPosition file offset).map (fun entity => ⟨sourceMap.revision, entity⟩)

def RevisionSourceMap.sourceOfEntity (sourceMap : RevisionSourceMap) (entity : IR.LocatedEntity) :
    Except (List IR.Diagnostic) (List IR.SourceSpan) :=
  if entity.revision == sourceMap.revision then .ok (sourceMap.map.find entity.entity)
  else .error [IR.Diagnostic.error "SYN-FRONTEND-REVISION-MISMATCH"
    "Source map and entity belong to different revisions."]

end Synthesis.Frontend
