import Synthesis

namespace Tests.RevisionIntegrity
open Synthesis Synthesis.IR Synthesis.Interop
set_option autoImplicit false

def revision (name : String) : RevisionRef := ⟨⟨["test", name]⟩, "1", none⟩
def tracked (a b : RevisionRef) : Stage Nat Nat := {
  id := .named "test" "tracked"
  run n := .ok ⟨n, { revisions := some (a, b), trace := [⟨a, b, [{}], [{}]⟩] }⟩ }

example : ((tracked (revision "A") (revision "B1")).andThen
    (tracked (revision "B2") (revision "C")) (.named "test" "chain") |>.run 0).isOk = false := by decide +kernel
example : ((tracked (revision "A") (revision "B1")).andThen
    (tracked (revision "B1") (revision "C")) (.named "test" "chain") |>.run 0).isOk = true := by decide +kernel

def migrationA : Migration Nat Nat := ⟨10, 11, tracked (revision "A") (revision "B1")⟩
def migrationB : Migration Nat Nat := ⟨11, 12, tracked (revision "B2") (revision "C")⟩
example : (match migrationA.andThen migrationB (.named "test" "migration") with
    | .error _ => true
    | .ok migration => !(migration.stage.run 0).isOk) = true := by decide +kernel

def emptySet : ExtensionSet := ⟨[], Extension.empty, by
  simp [Extension.combineMany, Extension.empty]
  funext op
  cases op
  rfl⟩
def module_ : IR.Module := { root := ⟨["test"]⟩, definitions := [{ id := ⟨["test"]⟩ }] }
def context : Frontend.ElaborationContext := {
  module := module_
  definition := module_.root
  extensions := emptySet }
example : (context.resolveName ⟨["missing"]⟩).isOk = false := by decide +kernel
example : ({ context with scopes := [[⟨⟨["alias"]⟩, {}, none⟩, ⟨⟨["alias"]⟩, {}, none⟩]] }
    |>.resolveName ⟨["alias"]⟩).isOk = false := by decide +kernel

def hierarchy : IR.Module := {
  root := ⟨["parent"]⟩
  definitions := [
    { id := ⟨["parent"]⟩, instances := [⟨"child", ⟨["childType"]⟩, [], [], {}⟩] },
    { id := ⟨["childType"]⟩, parameters := [⟨"p", ⟨.named "test" "scalar", []⟩, none⟩] }] }

example : Frontend.definitionOf hierarchy
    { definition := some hierarchy.root, instances := ["child"], steps := [.parameter "p"] } =
    some { definition := some ⟨["childType"]⟩ } := by decide +kernel

example : EvidenceStatus.notRun.render = "not-run" := rfl

def check : IO Unit := do
  let snapshot : ModuleRevision := ModuleRevision.create ⟨["test", "module"]⟩ "1" module_
  let located := snapshot.locate {}
  unless (snapshot.resolve located).isOk do throw (IO.userError "Own revision failed to resolve.")
  let stale := { located with revision := { located.revision with version := "2" } }
  if (snapshot.resolve stale).isOk then throw (IO.userError "Stale revision resolved.")
  let sourceMap : Frontend.RevisionSourceMap := ⟨snapshot.reference,
    ⟨[⟨{}, ⟨"fixture.lean", 2, 8⟩⟩]⟩⟩
  unless sourceMap.entityAtPosition "fixture.lean" 3 == [located] do
    throw (IO.userError "Source lookup lost revision identity.")
  unless (sourceMap.sourceOfEntity located).isOk do
    throw (IO.userError "Own revision source lookup failed.")
  if (sourceMap.sourceOfEntity stale).isOk then
    throw (IO.userError "Stale revision used a source map.")
  let report : EvidenceReport := {
    id := .named "test" "report"
    method := .named "test" "external-tool"
    subjects := [located]
    status := .inconclusive
    claim := .named "test" "claim"
    inputs := [snapshot.reference]
    statement := "The external tool did not establish the requested claim." }
  match Protocol.decodeEvidence (Protocol.encodeEvidence report) with
  | .error errors => throw (IO.userError s!"Evidence protocol rejected: {repr errors}")
  | .ok decoded => unless decide (decoded = report) do throw (IO.userError "Evidence protocol changed data.")
  let trace : Trace := ⟨revision "A", revision "B", [{}], [{}]⟩
  match Protocol.decodeTrace (Protocol.encodeTrace trace) with
  | .error errors => throw (IO.userError s!"Trace protocol rejected: {repr errors}")
  | .ok decoded => unless decide (decoded = trace) do throw (IO.userError "Trace protocol changed data.")
  unless report.subjects.head?.map (·.revision) == some snapshot.reference do
    throw (IO.userError "Evidence lost its revision.")

end Tests.RevisionIntegrity
