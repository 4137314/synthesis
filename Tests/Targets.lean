import Synthesis

namespace Tests.Targets
open Synthesis Synthesis.IR Synthesis.Frontend
set_option autoImplicit false

/-- These private dialect fixtures retain target-class information; they are not backends. -/
def id_ (family name : String) : ContractId := .named ("private." ++ family) name

def bits : TypeExpr := ⟨id_ "digital" "unsigned", [.integer 16]⟩
def clockType : TypeExpr := ⟨id_ "digital" "clock", []⟩

def clockPort (name : String) : Builder := port
  ⟨⟨name⟩, id_ "digital" "clock-interface", clockType, id_ "digital" "sink", []⟩

-- A downstream domain extends Lean syntax without editing the kernel's parser.
syntax "clock_port " str : doElem
macro_rules
  | `(doElem| clock_port $name:str) => `(doElem| Tests.Targets.clockPort $name)

def controller : Definition := engineering ⟨["private.digital", "controller"]⟩ where
  clock_port "clk"
  port ⟨"reset", id_ "digital" "signal", Standard.boolean, id_ "digital" "sink", []⟩
  parameter ⟨"width", Standard.rational, some (.literal Standard.rational (.rational 16))⟩
  operation (.node "register" (id_ "digital" "state") [] [⟨"q", bits, none⟩]
    [⟨id_ "digital" "reset-value", .integer 0⟩] [
      .node "next" (id_ "digital" "clocked-transition") [.variable "clk", .variable "reset",
        .apply (id_ "digital" "increment") [.variable "q"]] [] [] [] {}] {})

def simulation : Definition := engineering ⟨["private.continuous", "plant"]⟩ where
  parameter ⟨"mass", Standard.quantity (id_ "mechanics" "mass") .massDim, none⟩
  operation (.node "state" (id_ "continuous" "trajectory") []
    [⟨"x", ⟨id_ "continuous" "real-trajectory", []⟩, none⟩] [] [
      Standard.relation "initial" (id_ "continuous" "initial-equation") [.variable "x"],
      Standard.relation "dae" (id_ "continuous" "equal-zero")
        [.apply (id_ "continuous" "derivative") [.variable "x"]]] {})

def layout : Definition := engineering ⟨["private.geometry", "cell"]⟩ where
  operation (.node "outline" (id_ "geometry" "polygon") [] [] [
    ⟨id_ "geometry" "vertices", .sequence [
      .sequence [.integer 0, .integer 0], .sequence [.integer 10, .integer 0],
      .sequence [.integer 10, .integer 10], .sequence [.integer 0, .integer 10]]⟩,
    ⟨id_ "geometry" "layer", .integer 2⟩,
    ⟨id_ "geometry" "coordinate-unit", .tagged (id_ "units" "nanometre") []⟩] [] {})

def assembly : Definition := engineering ⟨["private.geometry", "assembly"]⟩ where
  instanceOf "cell-a" layout.id
  instanceOf "cell-b" layout.id
  operation (.node "place-b" (id_ "geometry" "placement") [] [] [
    ⟨id_ "geometry" "instance", .symbol "cell-b"⟩,
    ⟨id_ "geometry" "transform", .sequence [.integer 1, .integer 0, .integer 0,
      .integer 1, .integer 100, .integer 200]⟩] [] {})

def fem : Definition := engineering ⟨["private.fem", "specification"]⟩ where
  operation (.node "material" (id_ "fem" "material-region") [] [] [
    ⟨id_ "fem" "geometry-reference", .tagged (id_ "geometry" "cell") []⟩,
    ⟨id_ "fem" "constitutive-tensor", .sequence [.rational 200, .rational 0, .rational 200]⟩] [] {})
  operation (.node "boundary" (id_ "fem" "dirichlet") [] [] [
    ⟨id_ "fem" "boundary-id", .text "fixed-face"⟩,
    ⟨id_ "fem" "displacement", .sequence [.rational 0, .rational 0]⟩] [] {})

def systemSpec : Definition := engineering ⟨["private.systems", "aircraft"]⟩ where
  operation (.node "safe-temperature" (id_ "systems" "requirement") [] [] [
    ⟨id_ "systems" "external-id", .text "REQ-42"⟩] [
      Standard.relation "envelope" (id_ "systems" "assumption"),
      Standard.relation "limit" (id_ "systems" "guarantee")] {
        origin := some ⟨["requirements", "REQ-42"]⟩,
        source := some ⟨"requirements.lean", 100, 200⟩ })

example : (validate (design controller)).isOk = true := by decide
example : (validate (design simulation)).isOk = true := by decide
example : (validate (design assembly [layout])).isOk = true := by decide
example : (validate (design fem)).isOk = true := by decide
example : (validate (design systemSpec)).isOk = true := by decide

-- Structural compilation preserves every byte-shaped payload, nested body and lineage.
example (result : Validated) (h : compile (design assembly [layout]) = .ok result) :
    result.ast = design assembly [layout] := compile_preserves _ result h
example (result : Validated) (h : compile (design systemSpec) = .ok result) :
    result.ast.definitions = [systemSpec] := congrArg Module.definitions (compile_preserves _ result h)

/-- Systems-engineering relationships remain private contracts over shared structure. -/
def systemAssembly : Definition := engineering ⟨["private.systems", "assembly"]⟩ where
  instanceOf "requirements" systemSpec.id
  instanceOf "control" controller.id
  operation (.node "allocation" (id_ "systems" "allocation") [] [] [
    ⟨id_ "systems" "from", .symbol "requirements"⟩,
    ⟨id_ "systems" "to", .symbol "control"⟩] [] {})

def systemModel : IR.Module := design systemAssembly [systemSpec, controller]
example : systemModel.Structural := by decide +kernel
example : (systemModel.referencesToDefinition controller.id).length = 1 := by decide +kernel
example : (systemModel.operationsWith (id_ "systems" "requirement")).length = 1 := by decide +kernel

/-- Layout and logical entities can be linked without encoding a target ontology in IR. -/
def layoutTrace : Synthesis.Interop.Trace := ⟨
  [{ definition := some controller.id, steps := [.operation "register"] }],
  [{ definition := some layout.id, steps := [.operation "outline"] }]⟩
example : layoutTrace.source.all (fun r => (systemModel.findEntity r).isSome) = true := by decide +kernel
example : layoutTrace.target.all (fun r => ((design assembly [layout]).findEntity r).isSome) = true := by decide +kernel

end Tests.Targets
