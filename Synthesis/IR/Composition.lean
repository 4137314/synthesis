import Synthesis.IR.Extension
import Synthesis.IR.Entity

namespace Synthesis.IR
set_option autoImplicit false

/-- Fail-closed neutral extension. -/
def Extension.empty : Extension where
  type := fun _ => false
  literal := fun _ _ => false
  application := fun _ _ _ => none
  port := fun _ => false
  junction := fun _ _ _ => false
  operation := fun _ => false
  acceptAttribute := fun _ => false

/-- Ownership is declared separately from validation: rejection must not cause a
fallback to another package's interpretation of the same contract. -/
structure ExtensionPackage where
  id : ContractId
  contracts : List ContractId
  extension : Extension

/-- Pure composition requires exclusive contract ownership. A package may inspect
other contracts but handles only contracts in its manifest. No precedence rule exists. -/
def Extension.combineMany (packages : List ExtensionPackage) :
    Except (List Diagnostic) Extension :=
  let contracts := packages.flatMap (·.contracts)
  let conflicts := contracts.eraseDups.filter (fun id => (contracts.filter (· == id)).length > 1)
  if !conflicts.isEmpty then
    .error (conflicts.map fun id => {
      (Diagnostic.error "SYN-IR-CONTRACT-CONFLICT"
        "Extension manifests claim the same contract more than once.") with
      actual := some (.tagged id [])
      notes := (packages.filter (fun p => p.contracts.contains id)).map (fun p => reprStr p.id)
      remediation := some "Assign each semantic contract to one owner; compose shared dependencies once." })
  else if !(contracts.all ContractId.valid) then
    .error [Diagnostic.error "SYN-IR-INVALID-CONTRACT" "Extension manifest contains an invalid contract identity."]
  else
    let owner := fun id => (packages.find? (fun p => p.contracts.contains id)).map (·.extension)
    .ok {
      type := fun t => (owner t.constructor).any (fun e => e.type t)
      literal := fun t d => (owner t.constructor).any (fun e => e.literal t d)
      application := fun id terms types => (owner id).bind (fun e => e.application id terms types)
      port := fun p => (owner p.interface).any (fun e => e.port p)
      junction := fun m d j => (owner j.contract).any (fun e => e.junction m d j)
      operation := fun op => match op with
        | .node _ id _ _ _ _ _ => (owner id).any (fun e => e.operation op)
      acceptAttribute := fun a => (owner a.contract).any (fun e => e.acceptAttribute a)
      explain := fun m => packages.flatMap (fun p => p.extension.explain m) }

def Extension.combine (a b : ExtensionPackage) : Except (List Diagnostic) Extension :=
  Extension.combineMany [a, b]

/-- Explicit composed environment with retained ownership metadata for tooling. -/
structure ExtensionSet where
  packages : List ExtensionPackage
  extension : Extension
  composed : Extension.combineMany packages = .ok extension

def ExtensionSet.create (packages : List ExtensionPackage) : Except (List Diagnostic) ExtensionSet :=
  match h : Extension.combineMany packages with
  | .error errors => .error errors
  | .ok extension => .ok ⟨packages, extension, h⟩

def ExtensionSet.owner (extensions : ExtensionSet) (contract : ContractId) : Option ContractId :=
  (extensions.packages.find? (fun p => p.contracts.contains contract)).map (·.id)

def ExtensionSet.contracts (extensions : ExtensionSet) : List ContractId :=
  extensions.packages.flatMap (·.contracts)

/-- Reports the owner only when its operation-shape callback accepts. This is not
whole-definition typing or semantic interpretation. -/
def ExtensionSet.acceptedOperation (extensions : ExtensionSet) (operation : Operation) :
    Option ContractId :=
  if extensions.extension.operation operation then extensions.owner operation.contract else none

end Synthesis.IR
