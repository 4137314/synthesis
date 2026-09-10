import Synthesis

namespace Tests.Scale
open Synthesis Synthesis.IR
set_option autoImplicit false

def id_ (n : Nat) : QualifiedId := ⟨["scale", toString n]⟩

def model (count : Nat) : IR.Module := {
  root := ⟨["scale", "root"]⟩
  definitions := {
    id := ⟨["scale", "root"]⟩,
    instances := (List.range count).map (fun n => ⟨⟨toString n⟩, id_ n, [], [], {}⟩) } ::
    (List.range count).map (fun n => { id := id_ n }) }

/-- Default CI sizes test behavior, not performance thresholds. Larger sizes are opt-in. -/
def checkSize (count : Nat) : IO Unit := do
  let m := model count
  let index := m.buildIndex
  for n in List.range count do
    unless (index.findDefinition (id_ n)).isSome do throw (IO.userError "Indexed definition missing.")
  for n in List.range (min count 20) do
    unless decide (index.findDefinition (id_ n) = m.findDefinition (id_ n)) do
      throw (IO.userError "Index disagrees with canonical lookup.")
  unless m.walk.length == count * 2 + 2 do
    throw (IO.userError "Canonical traversal count changed.")
  match m.walkHierarchy 3 with
  | .error _ => throw (IO.userError "Wide hierarchy traversal failed.")
  | .ok entries => unless entries.length == count * 2 + 1 do
      throw (IO.userError "Hierarchy traversal count changed.")
  match IR.Module.decode m.encode (256 * 1024 * 1024) with
  | .error _ => throw (IO.userError "Scale round trip rejected.")
  | .ok decoded => unless decoded == m do throw (IO.userError "Scale round trip changed data.")

end Tests.Scale
