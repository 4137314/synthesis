import Lean
import Synthesis
import Tests.Main
import Synthesis.Domains
import Tests.RealElectronics
import Tests.Electronics

open Lean
/- Audit every imported project declaration against Lean's foundational assumptions.
In particular, compiler-trusted evaluation and proof holes are not accepted. -/
run_meta do
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in (← getEnv).constants.toList do
    let userName := (privateToUserName name).toString
    if "Synthesis.".isPrefixOf userName || "Tests.".isPrefixOf userName ||
        "_private.Tests.".isPrefixOf name.toString then
      for dependency in (← Lean.collectAxioms name) do
        unless permitted.contains dependency do
          throwError "{name} depends on unapproved assumption {dependency}"
