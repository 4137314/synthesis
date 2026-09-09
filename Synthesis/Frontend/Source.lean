import Lean
import Synthesis.Frontend.Scope

namespace Synthesis.Frontend
set_option autoImplicit false
open Lean Elab Term

/-- Attach syntax origin without erasing existing derivation lineage. -/
def sourceOperation (op : IR.Operation) (span : IR.SourceSpan) : IR.Operation :=
  match op with
  | .node name contract args results attrs body provenance =>
    .node name contract args results attrs body { provenance with source := some span }

/-- Domain syntax can reuse this term elaborator. The resulting portable operation
contains file/byte offsets only, never Syntax or elaborator state. -/
elab "sourced_operation " op:term : term => do
  let file ← getFileName
  let start := op.raw.getPos?.map (·.byteIdx) |>.getD 0
  let stop := op.raw.getTailPos?.map (·.byteIdx) |>.getD start
  let term ← `(Synthesis.Frontend.sourceOperation $op
    { source := $(quote file), start := $(quote start), stop := $(quote stop) })
  elabTerm term (some (mkConst ``IR.Operation))

end Synthesis.Frontend
