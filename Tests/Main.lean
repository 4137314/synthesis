import Synthesis
import Synthesis.Examples.Multiphysics
import Tests.Formal
import Tests.Engineering

open Synthesis Synthesis.IR Synthesis.Frontend Synthesis.Examples

private def rejects (d : Design) : Bool :=
  match compile d with
  | .error _ => true
  | .ok _ => false

example : rejects { electroOptic with
  connections := [⟨⟨"missing", "x"⟩, ⟨"receiver", "light"⟩⟩] } = true := by decide
example : rejects { electroOptic with
  components := electroOptic.components ++ electroOptic.components } = true := by decide
example : rejects { electroOptic with
  connections := [⟨⟨"driver", "voltage"⟩, ⟨"receiver", "light"⟩⟩] } = true := by decide
example : rejects { electroOptic with
  connections := electroOptic.connections ++ electroOptic.connections } = true := by decide
example : rejects { electroOptic with
  connections := [⟨⟨"receiver", "light"⟩, ⟨"modulator", "light"⟩⟩] } = true := by decide

example : rejects {
  name := "bad-dimension"
  components := [
  ⟨"source", "source", [⟨"out", .output, .quantity .electronics .voltage⟩], []⟩,
  ⟨"sink", "sink", [⟨"in", .input, .quantity .electronics .timeDim⟩], []⟩]
  connections := [⟨⟨"source", "out"⟩, ⟨"sink", "in"⟩⟩] } = true := by decide
example : rejects { name := "duplicate-port", components := [
  ⟨"source", "source", [⟨"out", .output, .quantum 1⟩,
    ⟨"out", .output, .quantum 1⟩], []⟩] } = true := by decide

private def quantumFanout : Design := {
  name := "invalid-cloning"
  components := [⟨"q", "prepare", [⟨"out", .output, .quantum 1⟩], []⟩,
    ⟨"a", "consume", [⟨"in", .input, .quantum 1⟩], []⟩,
    ⟨"b", "consume", [⟨"in", .input, .quantum 1⟩], []⟩]
  connections := [⟨⟨"q", "out"⟩, ⟨"a", "in"⟩⟩, ⟨⟨"q", "out"⟩, ⟨"b", "in"⟩⟩]
}
example : rejects quantumFanout = true := by decide
example : rejects { quantumFanout with connections := quantumFanout.connections.take 1 } = false := by decide
example : rejects { name := "zero", components := [
  ⟨"q", "prepare", [⟨"out", .output, .quantum 0⟩], []⟩] } = true := by decide
example : rejects { electroOptic with name := "" } = true := by decide
example : rejects electroOptic = false := by decide

-- Dimension mismatch is rejected by the Lean elaborator.
example : True := by
  fail_if_success
    have _ := Expr.add (Expr.literal (d := Dimension.lengthDim) 1)
      (Expr.literal (d := Dimension.timeDim) 1)
  trivial

def main : IO Unit := do
  match compile electroOptic with
  | .ok result =>
    unless result.ast == electroOptic.lower do throw (IO.userError "lowering changed graph")
    IO.println "synthesis: structural, domain, semantic and systems proofs passed"
  | .error e => throw (IO.userError s!"unexpected compile error: {repr e}")
