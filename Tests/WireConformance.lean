import Synthesis

namespace Tests.WireConformance
open Synthesis Synthesis.IR Lean
set_option autoImplicit false

def check : IO Unit := do
  let base := "Tests/Conformance/Wire/v1/"
  let manifest ← IO.FS.readFile (base ++ "manifest.json")
  let fixtures ← match Json.parse manifest >>= Json.getArr? with
    | .ok entries => pure entries
    | .error error => throw (IO.userError error)
  for fixture in fixtures do
    let file := (fixture.getObjValAs? String "file").toOption.getD ""
    let accepts := (fixture.getObjValAs? Bool "accept").toOption.getD false
    let raw ← IO.FS.readFile (base ++ file)
    match Module.decode raw with
    | .ok m =>
      unless accepts do throw (IO.userError s!"Invalid fixture accepted: {file}")
      let digest := (fixture.getObjValAs? String "digest").toOption.getD ""
      unless (fingerprint raw.toUTF8).hex == digest do
        throw (IO.userError s!"Fingerprint changed: {file}")
      unless m.encode == raw do throw (IO.userError s!"Canonical bytes changed: {file}")
    | .error errors =>
      if accepts then throw (IO.userError s!"Valid fixture rejected: {file}: {repr errors}")
      let code := (fixture.getObjValAs? String "code").toOption.getD ""
      unless errors.any (fun d => d.code == .named "synthesis.validation" code) do
        throw (IO.userError s!"Diagnostic changed: {file}")

end Tests.WireConformance
