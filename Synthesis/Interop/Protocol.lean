import Synthesis.Interop.Validation
import Synthesis.Core.Version

namespace Synthesis.Interop.Protocol
set_option autoImplicit false
open Lean IR.Wire

/-- Protocol-2 trace layout is explicit and independent from Lean deriving. -/
def encodeTrace (trace : Trace) : String :=
  (object [("protocol", toJson interopVersion),
    ("sourceRevision", toJson trace.sourceRevision), ("targetRevision", toJson trace.targetRevision),
    ("source", toJson trace.source), ("target", toJson trace.target)]).compress

def decodeTrace (text : String) : Except (List IR.Diagnostic) Trace := do
  let json ← IR.Wire.parse text
  let decoded : Except String Trace := do
    fields json ["protocol", "sourceRevision", "targetRevision", "source", "target"]
    let version ← json.getObjValAs? Nat "protocol"
    if version != interopVersion then throw "Unsupported interop protocol version."
    return ⟨← json.getObjValAs? RevisionRef "sourceRevision", ← json.getObjValAs? RevisionRef "targetRevision",
      ← json.getObjValAs? (List IR.EntityRef) "source", ← json.getObjValAs? (List IR.EntityRef) "target"⟩
  match decoded with
  | .ok trace => pure trace
  | .error message => throw [IR.Diagnostic.error "SYN-INTEROP-DECODE" message]

def statusName : EvidenceStatus → String
  | .passed => "passed" | .failed => "failed" | .inconclusive => "inconclusive"
  | .notRun => "not-run" | .assumed => "assumed"

/-- Reports remain claims. No serialized object is decoded as ProofEvidence. -/
def encodeEvidence (report : EvidenceReport) : String :=
  (object [("protocol", toJson interopVersion), ("id", toJson report.id),
    ("method", toJson report.method), ("subjects", toJson report.subjects),
    ("status", toJson (statusName report.status)), ("claim", toJson report.claim),
    ("tool", toJson report.tool), ("inputs", toJson report.inputs), ("outputs", toJson report.outputs),
    ("certificate", toJson report.certificate), ("statement", toJson report.statement),
    ("dependencies", toJson report.dependencies), ("provenance", toJson report.provenance)]).compress

def decodeEvidence (text : String) : Except (List IR.Diagnostic) EvidenceReport := do
  let json ← IR.Wire.parse text
  let decoded : Except String EvidenceReport := do
    fields json ["protocol", "id", "method", "subjects", "status", "claim", "tool", "inputs", "outputs",
      "certificate", "statement", "dependencies", "provenance"]
    let version ← json.getObjValAs? Nat "protocol"
    if version != interopVersion then throw "Unsupported interop protocol version."
    let status ← match ← json.getObjValAs? String "status" with
      | "passed" => pure EvidenceStatus.passed | "failed" => pure .failed
      | "inconclusive" => pure .inconclusive | "not-run" => pure .notRun | "assumed" => pure .assumed
      | _ => throw "Unknown evidence outcome."
    return {
      id := ← json.getObjValAs? ContractId "id"
      method := ← json.getObjValAs? ContractId "method"
      subjects := ← json.getObjValAs? (List IR.LocatedEntity) "subjects"
      status := status
      claim := ← json.getObjValAs? ContractId "claim"
      tool := ← json.getObjValAs? (Option ContractId) "tool"
      inputs := ← json.getObjValAs? (List RevisionRef) "inputs"
      outputs := ← json.getObjValAs? (List RevisionRef) "outputs"
      certificate := ← json.getObjValAs? (Option RevisionRef) "certificate"
      statement := ← json.getObjValAs? String "statement"
      dependencies := ← json.getObjValAs? (List ContractId) "dependencies"
      provenance := ← json.getObjValAs? IR.Provenance "provenance" }
  match decoded with
  | .ok report => pure report
  | .error message => throw [IR.Diagnostic.error "SYN-INTEROP-DECODE" message]

end Synthesis.Interop.Protocol
