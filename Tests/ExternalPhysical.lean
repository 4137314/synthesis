import Synthesis

namespace Tests.ExternalPhysical
open Synthesis Synthesis.IR Synthesis.Frontend Synthesis.Interop
set_option autoImplicit false

def cid (name : String) : ContractId := .named "private.physical" name

def plant : IR.Module := design (define ⟨["private", "plant"]⟩ (do
  parameter ⟨"coefficient", ⟨cid "real", []⟩, none⟩
  for name in (["a", "b", "c"] : List Symbol) do
    port ⟨name, cid "conservative", ⟨cid "across-through", []⟩, cid "oriented", []⟩
  junction "junction" (cid "balance") [⟨[], "a"⟩, ⟨[], "b"⟩, ⟨[], "c"⟩]
  operation (.node "state" (cid "trajectory") [] [⟨"x", ⟨cid "real", []⟩, none⟩] [] [
    .node "dae" (cid "equal-zero") [.apply (cid "derivative") [.variable "x"]] [] [] [] {}] {})))

/-- Private equation-system target retains symbolic terms and junction incidence.
No solver, causalization or numerical approximation is implied. -/
structure EquationSystem where
  parameters : List (QualifiedId × List Parameter)
  ports : List (QualifiedId × List Port)
  declarations : List Operation
  junctions : List Junction

def equations : Stage IR.Module EquationSystem where
  id := cid "equation-projection"
  run source :=
    let declarations := (source.entitiesOfKind .operation).filterMap fun cursor => match cursor.entity with
      | .operation op => some op | _ => none
    let junctions := (source.entitiesOfKind .junction).filterMap fun cursor => match cursor.entity with
      | .junction j => some j | _ => none
    if declarations.all (fun op => [cid "trajectory", cid "equal-zero"].contains op.contract) &&
        junctions.any (fun j => j.contract == cid "balance" && j.endpoints.length ≥ 3) then
      .ok ⟨⟨source.foldDefinitions [] (fun acc d => (d.id, d.foldParameters [] (fun ps p => p :: ps)) :: acc),
        source.foldDefinitions [] (fun acc d => (d.id, d.foldPorts [] (fun ps p => p :: ps)) :: acc),
        declarations, junctions⟩, { consumed := [cid "balance", cid "equal-zero"] }⟩
    else .error [Diagnostic.error "SYN-INTEROP-MISSING-REQUIREMENT"
      "Equation projection requires supported trajectory equations and multiway conservative incidence."]

example : plant.Structural := by decide +kernel
example : plant.concreteParameters = false := by decide +kernel
example : (equations.run plant).isOk = true := by decide +kernel

structure Polygon where
  coordinates : List Int
  layer : Nat
  technology : String
  deriving Repr, DecidableEq

def layout : IR.Module := design (define ⟨["private", "layout"]⟩ (do
  operation (.node "polygon" (cid "polygon") [] [] [
    ⟨cid "coordinates", .sequence [.integer 0, .integer 0, .integer 10, .integer 0, .integer 10, .integer 10]⟩,
    ⟨cid "layer", .integer 2⟩, ⟨cid "technology", .text "process-1"⟩] [] {})))

def polygon? (op : Operation) : Option Polygon := do
  if op.contract != cid "polygon" then none else pure ()
  let attrs := (Entity.operation op).attributes
  if attrs.length != 3 || !(attrs.all (fun a => [cid "coordinates", cid "layer", cid "technology"].contains a.contract)) then
    none else pure ()
  let .sequence coords ← (attrs.find? (·.contract == cid "coordinates")).map (·.value) | none
  let values ← coords.mapM (fun datum => match datum with | .integer n => some n | _ => none)
  if values.length < 6 || values.length % 2 != 0 then none else pure ()
  let .integer (.ofNat layer) ← (attrs.find? (·.contract == cid "layer")).map (·.value) | none
  let .text technology ← (attrs.find? (·.contract == cid "technology")).map (·.value) | none
  if technology.isEmpty then none else some ⟨values, layer, technology⟩

def polygons : Stage IR.Module (List Polygon) where
  id := cid "polygon-projection"
  run source :=
    match (source.entitiesOfKind .operation).mapM (fun cursor => match cursor.entity with
      | .operation op => polygon? op | _ => none) with
    | some (result@(_ :: _)) => .ok ⟨result, { consumed := [cid "coordinates", cid "layer", cid "technology"] }⟩
    | _ => .error [Diagnostic.error "SYN-INTEROP-MISSING-REQUIREMENT"
      "Layout fixture requires polygons, integer coordinate pairs, layer and technology mapping."]

example : (polygons.run layout).isOk = true := by decide +kernel
example : (polygons.run plant).isOk = false := by decide +kernel

end Tests.ExternalPhysical
