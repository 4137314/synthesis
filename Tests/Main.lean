import Tests.ExtensionComposition
import Tests.ExternalPhysical
import Tests.RevisionIntegrity
import Tests.ExternalBackend
import Tests.WireConformance
import Tests.Scale
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
  Tests.Scale.checkSize 100
  Tests.Scale.checkSize 1000
  Tests.WireConformance.check
  Tests.ExternalBackend.check
  Tests.RevisionIntegrity.check
  Tests.PublicAPI.check
  match Frontend.compile Examples.electroOptic with
  | .ok result =>
    unless result.ast == Examples.electroOptic do
      throw (IO.userError "structural compilation changed source")
    IO.println "synthesis: architecture, domain, semantic and systems proofs passed"
  | .error errors => throw (IO.userError s!"unexpected diagnostics: {repr errors}")
