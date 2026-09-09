import Synthesis

/- This fixture is intentionally a single public import, like a private downstream package. -/
namespace Tests.ExternalPackage.Acme.Hydraulics
open Synthesis Synthesis.IR Synthesis.Frontend Synthesis.Interop
set_option autoImplicit false

def pressureId : ContractId := .named "acme.hydraulics" "pressure"
def terminalId : ContractId := .named "acme.hydraulics" "terminal"
def balanceId : ContractId := .named "acme.hydraulics" "balance"
def relationId : ContractId := .named "acme.hydraulics" "constitutive"
def pressure : TypeExpr := ⟨pressureId, []⟩

def extension : Extension := { Extension.empty with
  type := (· == pressure)
  literal := fun t value => t == pressure && match value with
    | .rational _ => true | _ => false
  port := fun p => p.interface == terminalId && p.type == pressure
  junction := fun m d j => j.contract == balanceId && j.endpoints.all (fun endpoint =>
    (m.port? d endpoint).any (fun p => p.interface == terminalId))
  operation := fun op => op.contract == relationId }

def package : ExtensionPackage :=
  ⟨.named "acme" "hydraulics", [pressureId, terminalId, balanceId, relationId], extension⟩

def chamber : Definition := engineering ⟨["acme", "chamber"]⟩ where
  parameter ⟨"supply", pressure, none⟩
  port ⟨"terminal", terminalId, pressure, .named "acme.hydraulics" "oriented", []⟩
  operation (.node "law" relationId [.variable "supply", .variable "terminal"] [] [] [] {})

def plant : Definition := engineering ⟨["acme", "plant"]⟩ where
  parameter ⟨"pressure", pressure, none⟩
  instanceOf "a" chamber.id [⟨"supply", .variable "pressure"⟩]
  instanceOf "b" chamber.id [⟨"supply", .variable "pressure"⟩]
  instanceOf "c" chamber.id [⟨"supply", .variable "pressure"⟩]
  junction "balance" balanceId [⟨["a"], "terminal"⟩, ⟨["b"], "terminal"⟩, ⟨["c"], "terminal"⟩]

def model : IR.Module := design plant [chamber]

/-- A local relation is explicitly supplied by this package; matching type IDs do not
imply conservation. This example states a law rather than proving physical applicability. -/
def conservative (flow : Fin 3 → Rat) : Prop := flow 0 + flow 1 + flow 2 = 0

example : model.Structural := by decide +kernel
example : extension.accepts model = true := by decide +kernel
example : model.concreteParameters = false := by decide +kernel
example : (model.operationsWith relationId).length = 1 := by decide +kernel

/-- Private downstream prerequisite: only an explicitly literal-specialized source is
accepted. This is one prerequisite, not a claim of sufficient physical modeling. -/
def resolved : Interop.Requirement IR.Module :=
  ⟨.named "acme.export" "literal-parameters", fun m => m.concreteParameters = true⟩
def resolvedChecker : Checker resolved where
  check m := if h : m.concreteParameters = true then .ok ⟨h⟩ else
    .error [Diagnostic.error "SYN-INTEROP-MISSING-REQUIREMENT"
      "The consumer requires literal parameters; run explicit specialization first."]

def inspectionExporter : Exporter IR.Module String where
  target := .named "acme" "inspection-text"
  requirement := resolved
  checker := resolvedChecker
  emit m _ := .ok ⟨m.renderSummary, {
    consumed := [pressureId]
    erased := [relationId]
    trace := [⟨[{ definition := some plant.id }], [{}]⟩] }⟩

example : (inspectionExporter.run model).isOk = false := by decide +kernel

/-- An ordinary stage is not advertised as preserving meaning. -/
def identityStage : Stage IR.Module IR.Module where
  id := .named "acme" "identity"
  run m := .ok ⟨m, {}⟩

example : Establishes identityStage (fun a b => a = b) := by
  intro a result h
  cases h
  rfl

example : ((Extension.combine package
    ⟨.named "private" "empty", [], Extension.empty⟩)).isOk = true := by decide +kernel

example : (match Extension.combineMany [package] with
    | .ok composed => composed.accepts model
    | .error _ => false) = true := by decide +kernel
example : (match Extension.combineMany [package] with
    | .ok composed => composed.type ⟨.named "unknown" "type", []⟩
    | .error _ => true) = false := by decide +kernel

example : (DesignBuilder.finish plant.id (do
    let _ ← DesignBuilder.addDefinition chamber
    let _ ← DesignBuilder.addDefinition plant
    pure ())).isOk = true := by decide +kernel
example : (DesignBuilder.finish chamber.id (do
    let _ ← DesignBuilder.addDefinition chamber
    let _ ← DesignBuilder.addDefinition chamber
    pure ())).isOk = false := by decide +kernel

example : (match model.index with
    | .ok index => (index.findDefinition chamber.id).isSome
    | .error _ => false) = true := by decide +kernel

end Tests.ExternalPackage.Acme.Hydraulics
