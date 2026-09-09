import Synthesis

namespace Tests.Architecture
open Synthesis Synthesis.IR Synthesis.Frontend
set_option autoImplicit false

/-- Private contracts require only public imports. No central domain list is involved. -/
def cid (name : String) : ContractId := .named "acme.private" name
def scalar : TypeExpr := Standard.rational
def bitVector : TypeExpr := ⟨cid "bits", [.integer 8]⟩
def terminalType : TypeExpr := ⟨cid "hydraulic-terminal", []⟩
def sourceRole := cid "source"
def sinkRole := cid "sink"
def terminalRole := cid "terminal"

def ext : Extension where
  type ty := ty == scalar || ty == bitVector || ty == terminalType
  literal ty value := match value with
    | .rational _ => ty == scalar
    | .integer n => ty == bitVector && n >= 0 && n < 256
    | _ => false
  application op _ types :=
    if op == cid "multiply" && types == [scalar, scalar] then some scalar else none
  port p := (p.interface == cid "signal" && (p.role == sourceRole || p.role == sinkRole) &&
      p.type == bitVector) ||
    (p.interface == cid "hydraulic" && p.role == terminalRole && p.type == terminalType)
  junction m d j :=
    if j.contract == cid "signal" then Connector.signal sourceRole sinkRole m d j
    else if j.contract == cid "resource" then Connector.resource sourceRole sinkRole m d j
    else if j.contract == cid "hydraulic" then Connector.conservative terminalRole m d j
    else false
  operation op := match op with
    | .node _ contract args results attrs _ _ =>
      contract == cid "equation" && args.length == 1 && results.isEmpty && attrs.isEmpty
  acceptAttribute _ := false

def leaf : Definition := engineering ⟨["acme", "leaf"]⟩ where
  port ⟨"out", cid "signal", bitVector, sourceRole, []⟩
  port ⟨"in", cid "signal", bitVector, sinkRole, []⟩

def root : Definition := engineering ⟨["acme", "root"]⟩ where
  instanceOf "a" leaf.id
  instanceOf "b" leaf.id
  instanceOf "c" leaf.id
  junction "bus" (cid "signal") [⟨["a"], "out"⟩, ⟨["b"], "in"⟩, ⟨["c"], "in"⟩]

def module_ : Module := design root [leaf]
example : (ext.check module_).isOk = true := by decide +kernel
example : module_.definition? leaf.id = some leaf := by decide +kernel
example : module_.port? root ⟨["b"], "in"⟩ = some ⟨"in", cid "signal", bitVector, sinkRole, []⟩ := by decide +kernel

-- Multiway signal fanout is legal; the same topology is not resource-safe.
example : Connector.resource sourceRole sinkRole module_ root (⟨"bus", cid "signal", [⟨["a"], "out"⟩, ⟨["b"], "in"⟩, ⟨["c"], "in"⟩], [], {}⟩) = false := by decide +kernel

-- Dangling hierarchy paths, recursion, duplicate declarations and invalid roots fail.
example : (validate { module_ with root := ⟨["missing"]⟩ }).isOk = false := by decide +kernel
example : (validate (design { root with instances := [⟨"self", root.id, [], [], {}⟩] })).isOk = false := by decide +kernel
example : (validate { module_ with definitions := [root, leaf, leaf] }).isOk = false := by decide +kernel
example : (validate (design { root with junctions := [⟨"bad", cid "signal",
    [⟨["missing"], "in"⟩], [], {}⟩] } [leaf])).isOk = false := by decide +kernel

-- Symbolic defaults are ordered bindings, not unchecked strings or implicit approximation.
def symbolic : Definition := engineering ⟨["acme", "symbolic"]⟩ where
  parameter ⟨"gain", scalar, none⟩
  parameter ⟨"square", scalar, some (.apply (cid "multiply") [.variable "gain", .variable "gain"])⟩
  operation (Standard.relation "constraint" (cid "equation") [.variable "square"])

def specialized : Module := { design symbolic with bindings := [⟨"gain", .literal scalar (.rational 3)⟩] }
example : (ext.check specialized).isOk = true := by decide +kernel
example : (ext.check (design symbolic)).isOk = true := by decide +kernel
example : (ext.check { specialized with bindings := [⟨"gain", .literal bitVector (.integer 3)⟩] }).isOk = false := by decide +kernel
example : ext.infer [] (.variable "unbound") = none := by decide +kernel
example : ext.infer [] (.apply (cid "unknown") []) = none := by decide +kernel
example : ext.infer [] (.literal bitVector (.integer 256)) = none := by decide +kernel
example : (ext.check (design { symbolic with parameters := symbolic.parameters.reverse })).isOk = false := by decide +kernel

-- Unknown semantic attributes cannot pass a handler that knows only the core structure.
example : (validate { module_ with attributes := [⟨cid "private-geometry", .sequence []⟩] }).isOk = true := by decide +kernel
example : (ext.check { module_ with attributes := [⟨cid "private-geometry", .sequence []⟩] }).isOk = false := by decide +kernel

-- Independent extensions can retain nested behavior and geometry without central cases.
def stress (owner : String) : Definition := engineering ⟨[owner, "system"]⟩ where
  parameter ⟨"external", ⟨.named owner "field", []⟩, none⟩
  operation (.node "behavior" (.named owner "hybrid") [] [] []
    [Standard.relation "initial" (.named owner "initialization"),
     Standard.relation "derivative" (.named owner "differential-equation"),
     Standard.relation "fault" (.named owner "degraded-mode")] {})
  operation (.node "geometry" (.named owner "polygon") [] []
    [⟨.named owner "coordinates", .sequence [.sequence [.rational 0, .rational 1],
      .sequence [.rational 2, .rational 3], .sequence [.rational 4, .rational 0]]⟩,
     ⟨.named owner "layer", .integer 7⟩,
     ⟨.named owner "placement", .sequence [.rational 10, .rational 20]⟩] [] {})

example : (["hydraulics", "aerodynamics", "rf", "structural-fem", "navigation", "nuclear"].map
    (fun owner => (validate (design (stress owner))).isOk)) = List.replicate 6 true := by decide +kernel

-- Sufficiency is evidence about the actual source. Geometry is never inferred from a name.
def hasPolygon (op : Operation) : Bool := match op with
  | .node _ contract _ _ attrs _ _ =>
    contract == .named "layout" "polygon" &&
    attrs.any (fun a => a.contract == .named "layout" "coordinates" &&
      match a.value with
      | .sequence points => points.length >= 3 && points.all (fun p =>
        match p with
        | .sequence [.rational _, .rational _] => true
        | _ => false)
      | _ => false) &&
    attrs.any (fun a => a.contract == .named "layout" "layer" &&
      match a.value with | .integer n => n >= 0 | _ => false)

def hasGeometry : Interop.Requirement Module :=
  ⟨cid "polygon-information", fun m =>
    m.definitions.any (fun d => d.operations.any hasPolygon) = true⟩

def geometryChecker : Interop.Checker hasGeometry where
  check m := if h : m.definitions.any (fun d => d.operations.any hasPolygon) = true then .ok ⟨h⟩ else .error [{
    code := cid "E-MISSING-GEOMETRY", message := "Geometry is required by this lowering.",
    scope := some m.root, remediation := some "Supply geometry or run an explicit geometry-producing refinement." }]

example : (geometryChecker.check module_).isOk = false := by decide +kernel
example : (geometryChecker.check (design (stress "layout"))).isOk = true := by decide +kernel

-- Quantity kind identity survives equal dimensions, including stress and energy density.
example : Standard.quantity (cid "stress") .pressure ≠
    Standard.quantity (cid "energy-density") .pressure := by decide +kernel

-- Schema mismatches, cross-interface wiring and duplicated drivers cannot be accepted.
example : (validate { module_ with schema := 2 }).isOk = false := by decide +kernel
example : Connector.homogeneous [
    ⟨"p", cid "electrical", terminalType, terminalRole, []⟩,
    ⟨"p", cid "thermal", terminalType, terminalRole, []⟩] = false := by decide +kernel
example : (ext.check (design { root with junctions := [⟨"drivers", cid "signal",
    [⟨["a"], "out"⟩, ⟨["b"], "out"⟩, ⟨["c"], "in"⟩], [], {}⟩] } [leaf])).isOk = false := by decide +kernel
example : (ext.check (design { root with junctions := root.junctions ++
    [⟨"reuse", cid "signal", [⟨["a"], "out"⟩, ⟨["b"], "in"⟩], [], {}⟩] } [leaf])).isOk = false := by decide +kernel

-- A genuine conservative three-terminal network has no designated producer.
def physical : Definition := engineering ⟨["acme", "physical"]⟩ where
  port ⟨"a", cid "hydraulic", terminalType, terminalRole, []⟩
  port ⟨"b", cid "hydraulic", terminalType, terminalRole, []⟩
  port ⟨"c", cid "hydraulic", terminalType, terminalRole, []⟩
  junction "node" (cid "hydraulic") [⟨[], "a"⟩, ⟨[], "b"⟩, ⟨[], "c"⟩]
example : (ext.check (design physical)).isOk = true := by decide +kernel

example : (design symbolic).concreteParameters = false := by decide +kernel
-- Binding gain does not pretend that the derived square has already been evaluated.
example : specialized.concreteParameters = false := by decide +kernel
example : ({ specialized with bindings := specialized.bindings ++
    [⟨"square", .literal scalar (.rational 9)⟩] } : Module).concreteParameters = true := by decide +kernel

-- Duplicate nested operation identities are rejected independently of dialect typing.
example : (validate (design { leaf with operations := [
    .node "region" (cid "region") [] [] []
      [Standard.relation "same" (cid "one"), Standard.relation "same" (cid "two")] {}] })).isOk = false := by decide +kernel

-- A name alone never satisfies even the illustrative polygon prerequisite.
example : (geometryChecker.check (design { leaf with operations :=
    [Standard.relation "geometry" (cid "unknown")] })).isOk = false := by decide +kernel

-- Heterogeneous local spaces compose via projections; no universal state record is required.
def localNumber : Semantics.LocalRelation (Nat × Bool) :=
  ⟨Nat, Prod.fst, fun n => n > 0⟩
def localFlag : Semantics.LocalRelation (Nat × Bool) :=
  ⟨Bool, Prod.snd, fun flag => flag = true⟩
example : Semantics.assemble [localNumber, localFlag] (1, true) := by
  simp [Semantics.assemble, Semantics.LocalRelation.behavior, localNumber, localFlag]

-- Lossy projection is a stage to a different representation type, with explicit erasure.
def namesProjection : Interop.Stage Module (List QualifiedId) where
  id := cid "names-projection"
  run m := .ok ⟨m.definitions.map (·.id), {
    erased := [cid "behavior", cid "interfaces", cid "parameters"],
    consumed := [cid "definitions"] }⟩
example : Interop.Establishes namesProjection (fun m ids => ids = m.definitions.map (·.id)) := by
  intro m result h
  cases h
  rfl

#engineering.check module_

-- Value-dependent type families inspect the original arguments as well as their types.
def sizedExt : Extension := { ext with
  type := fun ty => ty.constructor == cid "bits" &&
    match ty.arguments with
    | [.integer width] => width > 0 && width <= 256
    | _ => false
  application := fun op args types => match args, types with
    | [.literal _ (.integer width)], [ty] =>
      if op == cid "zero-vector" && ty == bitVector && width > 0 then
        some ⟨cid "bits", [.integer width]⟩ else none
    | _, _ => none }
example : sizedExt.infer [] (.apply (cid "zero-vector") [.literal bitVector (.integer 16)]) =
    some ⟨cid "bits", [.integer 16]⟩ := by decide
example : sizedExt.infer [] (.apply (cid "zero-vector") [.literal bitVector (.integer 0)]) =
    none := by decide
example : sizedExt.infer [("width", bitVector)] (.apply (cid "zero-vector") [.variable "width"]) =
    none := by decide

end Tests.Architecture
