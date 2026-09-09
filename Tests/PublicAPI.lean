import Synthesis

namespace Tests.PublicAPI
open Synthesis Synthesis.IR
set_option autoImplicit false

private def assemblyId : QualifiedId := ⟨["private", "hydraulic", "assembly"]⟩
private def ty : TypeExpr := ⟨.named "private.hydraulic" "pressure", []⟩
private def model (n : Nat) : IR.Module := {
  root := assemblyId
  annotations := [⟨⟨["note"]⟩, .text "unicode λ / quoted \"value\""⟩]
  attributes := [⟨.named "private" "payload", .tagged (.named "private" "tag")
    [.sequence [.symbol "s", .integer (-4), .rational (1/3)]]⟩]
  provenance := {
    source := some ⟨"fixture.lean", 0, 10⟩,
    origin := some ⟨["imported"]⟩, parents := [⟨["parent"]⟩],
    transformation := some (.named "private" "derived") }
  definitions := [{
    id := assemblyId
    parameters := [⟨"pressure", ty, none⟩]
    operations := [.node "constraint" (.named "private.hydraulic" "envelope")
      [.literal ty (.rational (n : Rat))] [] []
      [.node "nested" (.named "private.hydraulic" "relation") [] [] [] [] {}] {}] }] }

example : ((model 0).findEntity {
    definition := some assemblyId
    steps := [.operation "constraint", .operation "nested"] }).isSome = true := by decide +kernel
example : ((model 0).findEntity {
    definition := some assemblyId
    steps := [.operation "missing"] }).isSome = false := by decide +kernel
example : (model 0).walk.length = 7 := by decide +kernel
example : ((model 0).walkHierarchy 0).isOk = false := by decide +kernel
example : (Extension.combine
    ⟨.named "private" "a", [ty.constructor], Extension.empty⟩
    ⟨.named "private" "b", [ty.constructor], Extension.empty⟩).isOk = false := by decide +kernel
example : (Extension.combineMany []).isOk = true := by decide +kernel

private def goldenModel : IR.Module :=
  { root := ⟨["fixture"]⟩, definitions := [{ id := ⟨["fixture"]⟩ }] }
private def golden : String := r#"{"format":1,"module":{"annotations":[],"attributes":[],"bindings":[],"definitions":[{"annotations":[],"attributes":[],"id":{"segments":["fixture"]},"instances":[],"junctions":[],"operations":[],"parameters":[],"ports":[],"provenance":{"origin":null,"parents":[],"source":null,"transformation":null}}],"provenance":{"origin":null,"parents":[],"source":null,"transformation":null},"root":{"segments":["fixture"]},"schema":3},"schema":3}"#

private def aRef : EntityRef := { definition := some ⟨["a"]⟩, steps := [.port "p"] }
private def bRef : EntityRef := { definition := some ⟨["b"]⟩, steps := [.operation "o"] }
private def cRef : EntityRef := { definition := some ⟨["c"]⟩, steps := [.result "r"] }

example : (Interop.Trace.compose [⟨[aRef], [bRef]⟩] [⟨[bRef], [cRef]⟩]).length = 1 := by decide +kernel
example : (Interop.Trace.compose [⟨[aRef], [bRef]⟩] [⟨[aRef], [cRef]⟩]).isEmpty = true := by decide +kernel
example : renderId ⟨["a/b", "c"]⟩ = "3:a/b/1:c" := by decide +kernel
example : (Frontend.SourceDocument.range ⟨"x", "a\nb"⟩ ⟨"x", 2, 3⟩) =
    some (⟨1, 0⟩, ⟨1, 1⟩) := by decide +kernel
example : (Frontend.SourceDocument.range ⟨"x", "a"⟩ ⟨"x", 2, 1⟩) = none := by decide +kernel

private def sourced : Operation := sourced_operation
  (.node "source-test" (.named "private" "relation") [] [] [] [] {})
example : (Entity.operation sourced).provenance.source.isSome = true := by decide +kernel

private def identityStage : Interop.Stage Nat Nat :=
  ⟨.named "test" "identity", fun n => .ok ⟨n, {}⟩⟩
example : ((Interop.Migration.andThen ⟨3, 3, identityStage⟩ ⟨4, 4, identityStage⟩
    (.named "test" "compose"))).isOk = false := by decide +kernel
example : ((Interop.Migration.andThen ⟨3, 3, identityStage⟩ ⟨3, 3, identityStage⟩
    (.named "test" "compose"))).isOk = true := by decide +kernel

private def equalityValidator : Interop.TranslationValidator Nat Nat Eq where
  id := .named "test" "equality-validator"
  check source target := if h : source = target then .ok ⟨h⟩ else
    .error [Diagnostic.error "SYN-INTEROP-RELATION" "Candidate differs from the source."]
example : (equalityValidator.certify 2 3).isOk = false := by decide +kernel
example : (equalityValidator.certify 2 2).isOk = true := by decide +kernel

private def realizationProblem : Design.RealizationProblem Nat Nat := {
  specification := ⟨.named "test" "positive", ⟨fun _ => True, fun x => x > 0⟩⟩
  technology := ⟨.named "test" "bounded", fun n => n ≤ 10, []⟩
  behavior := fun n x => x = n }
private def realization : Design.CertifiedRealization realizationProblem := {
  candidate := 1
  admissible := by change 1 ≤ 10; decide +kernel
  feasible := ⟨1, rfl, True.intro⟩
  satisfies := by intro x hx _; change x = 1 at hx; subst x; change 1 > 0; decide +kernel }
example : realization.candidate = 1 := rfl

/-- Runtime conformance checks exercise recursive decoder code, not theorem evidence. -/
def check : IO Unit := do
  unless goldenModel.encode == golden do throw (IO.userError "Format-1 golden fixture changed.")
  match IR.Module.decode golden with
  | .ok m => unless m == goldenModel do throw (IO.userError "Golden decode changed.")
  | .error _ => throw (IO.userError "Golden fixture rejected.")
  let unknown := golden.replace "\"format\":1" "\"unknown\":0,\"format\":1"
  if (IR.Module.decode unknown).isOk then throw (IO.userError "Unknown field was silently discarded.")
  match IR.Module.decode "{\"format\":99,\"schema\":3}" with
  | .error (diagnostic :: _) =>
    unless diagnostic.code == .named "synthesis.validation" "SYN-IR-UNSUPPORTED-VERSION" do
      throw (IO.userError "Version diagnostic code changed.")
  | _ => throw (IO.userError "Version rejection produced no diagnostic.")
  for n in List.range 32 do
    let m := model n
    match IR.Module.decode m.encode with
    | .error ds => throw (IO.userError (String.intercalate "\n" (ds.map Diagnostic.render)))
    | .ok decoded => unless decoded == m do throw (IO.userError "IR round trip changed the model.")
    for cursor in m.walk do
      unless decide (m.findEntity cursor.reference = some cursor.entity) do
        throw (IO.userError "Traversal produced an unresolved locator.")
  if (IR.Module.decode golden 1).isOk then throw (IO.userError "Byte limit ignored.")
  if (IR.Module.decode golden 16777216 1).isOk then throw (IO.userError "Depth limit ignored.")
  if (IR.Module.decode "{}").isOk then throw (IO.userError "Malformed envelope accepted.")
  if (IR.Module.decode "{\"format\":99,\"schema\":3}").isOk then
    throw (IO.userError "Unsupported version accepted.")

end Tests.PublicAPI
