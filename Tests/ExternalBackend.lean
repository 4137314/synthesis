import Synthesis

namespace Tests.ExternalBackend
open Synthesis Synthesis.IR Synthesis.Interop
set_option autoImplicit false

def register : ContractId := .named "private.rtl" "register"

/-- Private target syntax. It is not VHDL and carries no timing/realizability claim. -/
structure Target where
  width : Nat
  registers : Nat
  deriving Repr, DecidableEq

def targetText (target : Target) : String := s!"width={target.width};registers={target.registers}"

def sourceRevision (source : IR.Module) : RevisionRef :=
  ⟨⟨["private.rtl", "source"]⟩, "1", some (fingerprint source.encode.toUTF8)⟩
def targetRevision (target : Target) : RevisionRef :=
  ⟨⟨["private.rtl", "target"]⟩, "1", some (fingerprint (targetText target).toUTF8)⟩

/-- Only positive literal widths and explicitly recognized operations are supported. -/
def project (source : IR.Module) : Option Target := do
  let .parameter parameter ← source.findEntity {
    definition := some source.root
    steps := [.parameter "width"] } | none
  let some (.literal _ (.integer width)) := parameter.value | none
  if width ≤ 0 then none else pure ()
  if !(source.entitiesOfKind .operation).all (fun cursor => match cursor.entity with
    | .operation operation => operation.contract == register
    | _ => false) then none else pure ()
  pure ⟨width.toNat, (source.operationsWith register).length⟩

def requirement : Interop.Requirement IR.Module :=
  ⟨.named "private.rtl" "sufficient", fun source => (project source).isSome = true⟩
def checker : Checker requirement where
  check source := if h : (project source).isSome = true then .ok ⟨h⟩ else
    .error [Diagnostic.error "SYN-INTEROP-MISSING-REQUIREMENT"
      "RTL fixture requires positive literal width and only registered state operations."]

def lower : Exporter IR.Module Target where
  target := .named "private.rtl" "ast"
  requirement := requirement
  checker := checker
  emit source _ := match project source with
    | none => .error [Diagnostic.error "SYN-INTEROP-MISSING-REQUIREMENT" "Unsupported source."]
    | some target => .ok ⟨target, {
      revisions := some (sourceRevision source, targetRevision target)
      consumed := [register]
      trace := [⟨sourceRevision source, targetRevision target,
        [{ definition := some source.root, steps := [.parameter "width"] }],
        [{ steps := [.parameter "width"] }]⟩] }⟩

/-- Independently certifies a structural projection, not electrical/RTL equivalence. -/
def validator : TranslationValidator IR.Module Target (fun source target => project source = some target) where
  id := .named "private.rtl" "projection-validator"
  check source target := if h : project source = some target then .ok ⟨h⟩ else
    .error [Diagnostic.error "SYN-INTEROP-TRANSLATION" "Target does not match the source projection."]

def encode : Stage Target String where
  id := .named "private.rtl" "text-encoding"
  run target := .ok ⟨targetText target, {
    revisions := some (targetRevision target,
      ⟨⟨["private.rtl", "artifact"]⟩, "1", some (fingerprint (targetText target).toUTF8)⟩) }⟩

def widthEncoding : Design.Encoding Nat where
  type := ⟨.named "private.rtl" "width", []⟩
  encode n := .integer n
  decode value := match value with
    | .integer (.ofNat n) => some n
    | _ => none
  exact _ := rfl

def source (width : Option Nat) : IR.Module := Frontend.design
  (Frontend.define ⟨["private.rtl", "module"]⟩ (do
    Frontend.parameter ⟨"width", widthEncoding.type, width.map widthEncoding.literal⟩
    Frontend.operation (.node "state" register [] [] [] [] {})))

example : (lower.run (source none)).isOk = false := by decide +kernel
example : (project (source (some 8))) = some ⟨8, 1⟩ := by decide +kernel
example : (validator.certify (source (some 8)) ⟨7, 1⟩).isOk = false := by decide +kernel
example : (validator.certify (source (some 8)) ⟨8, 1⟩).isOk = true := by decide +kernel

/-- Exercise revision computation and encoding at runtime, without theorem claims about hashes. -/
def check : IO Unit := do
  let stage : Stage IR.Module Target := ⟨.named "private.rtl" "lower", lower.run⟩
  match (stage.andThen encode (.named "private.rtl" "compile")).run (source (some 8)) with
  | .error errors => throw (IO.userError s!"External pipeline failed: {repr errors}")
  | .ok result => unless result.value == "width=8;registers=1" do
      throw (IO.userError "External artifact changed.")

end Tests.ExternalBackend
