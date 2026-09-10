import Synthesis

namespace Tests.ExtensionComposition
open Synthesis Synthesis.IR
set_option autoImplicit false

def package (owner name : String) : ExtensionPackage := {
  id := .named owner "package"
  contracts := [.named owner name]
  extension := { Extension.empty with
    type := fun type => type.constructor == .named owner name
    operation := fun op => op.contract == .named owner name && op.name != "rejected" } }

def electrical := package "private.electrical" "behavior"
def thermal := package "private.thermal" "behavior"
def geometry := package "private.geometry" "polygon"
def company := package "company" "constraint"

example : (ExtensionSet.create [electrical, thermal, geometry, company]).isOk = true := by decide +kernel
example : (ExtensionSet.create [company, package "company" "different"]).isOk = true := by decide +kernel
example : (ExtensionSet.create [electrical, electrical]).isOk = false := by decide +kernel

def mixed : IR.Module := Frontend.design (Frontend.define ⟨["private", "mixed"]⟩ (do
  Frontend.operation (.node "outer" (.named "private.electrical" "behavior") [] [] [] [
    .node "inner" (.named "private.thermal" "behavior") [] [] [] [] {}] {})))

example : (match ExtensionSet.create [electrical, thermal] with
    | .error _ => false
    | .ok active => active.extension.accepts mixed) = true := by decide +kernel
example : (match ExtensionSet.create [electrical, thermal] with
    | .error _ => true
    | .ok active => (active.acceptedOperation
        (.node "rejected" (.named "private.electrical" "behavior") [] [] [] [] {})).isSome) = false := by decide +kernel
example : (match ExtensionSet.create [electrical, thermal] with
    | .error _ => none
    | .ok active => active.owner (.named "private.thermal" "behavior")) = some thermal.id := by decide +kernel

end Tests.ExtensionComposition
