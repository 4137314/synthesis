import Tests.ExternalPackage
import Tests.PublicAPI
import Synthesis
import Synthesis.Examples.Multiphysics
import Tests.Formal
import Tests.Engineering
import Tests.Architecture
import Tests.Targets

open Synthesis

def main : IO Unit := do
  Tests.PublicAPI.check
  match Frontend.compile Examples.electroOptic with
  | .ok result =>
    unless result.ast == Examples.electroOptic do
      throw (IO.userError "structural compilation changed source")
    IO.println "synthesis: architecture, domain, semantic and systems proofs passed"
  | .error errors => throw (IO.userError s!"unexpected diagnostics: {repr errors}")
