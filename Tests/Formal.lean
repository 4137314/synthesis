import Synthesis.Examples.Assurance

open Synthesis Synthesis.Logic Synthesis.Semantics Synthesis.Physics
open Synthesis.Examples.Assurance

-- The rich semantic frontend preserves the source relation.
example : (Frontend.compileModel design).isOk = true := by decide

-- An implementation cannot silently strengthen its environmental assumptions.
example : ¬Contract.Refines
    (⟨fun x : Bool => x = true, fun x => x = true⟩)
    (⟨fun _ => True, fun x => x = true⟩) := by
  intro h
  have impossible := h.1 false trivial
  cases impossible

-- Individually feasible behaviors may have an impossible joint composition.
example : ¬Contract.Compatible (fun x : Bool => x = true) (fun x => x = false)
    ⟨fun _ => True, fun _ => True⟩ ⟨fun _ => True, fun _ => True⟩ := by
  intro h
  obtain ⟨x, ht, hf, _, _⟩ := h.witness
  cases ht
  cases hf

-- Dimensional equations cannot conflate time and length.
example : True := by
  fail_if_success
    have _ : Equation Int Dimension.lengthDim :=
      ⟨⟨1⟩, (⟨1⟩ : Quantity Int Dimension.timeDim)⟩
  trivial

-- A nonzero generated inventory invalidates an assertion of closed conservation.
example : ¬(Balance.Holds (Scalar := Int) (d := inventoryDimension)
    ⟨⟨4⟩, ⟨4⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩⟩) := by simp [Balance.Holds]

-- Missing whole-module coverage cannot become an unconstrained behavior.
example (m : IR.Module) (x : Unit) :
    ¬(Semantics.Interpretation.mk (fun _ => none)).Meaning m x :=
  Semantics.unsupported rfl x

-- Refinement does not manufacture feasibility.
example : Interop.Refines (fun _ : Unit => False) (fun _ : Unit => True) id :=
  fun _ h => False.elim h

-- Rich composition rejects duplicate placement identities; semantic coverage cannot bypass it.
example : (Frontend.compileSystem { pairedInventory with
    parts := pairedInventory.parts ++ pairedInventory.parts }).isOk = false := by decide
