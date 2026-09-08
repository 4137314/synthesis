import Synthesis.Examples.Assurance

open Synthesis Synthesis.Logic Synthesis.Semantics Synthesis.Physics
open Synthesis.Examples.Assurance

-- The semantic frontend accepts the known interpretation without changing its graph.
example : (Frontend.compileModel design interpretation model.supported).isOk = true := by decide

-- Semantic coverage cannot bypass structural checking.
example : (Frontend.compileModel { design with name := "" }
    interpretation model.supported).isOk = false := by decide

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

-- Coverage includes couplings: recognizing all components alone is insufficient.
example : ¬interpretation.Supported {
    design.lower with connections := [⟨⟨"inventory", "a"⟩, ⟨"inventory", "b"⟩⟩] } := by
  intro h
  obtain ⟨meaning, found⟩ := h.2 ⟨⟨"inventory", "a"⟩, ⟨"inventory", "b"⟩⟩ (by simp)
  cases found

-- A pass must preserve behavior, not merely return a structurally valid graph.
example : ¬(∀ x, impossible.behavior x ↔ (fun _ : Unit => True) x) := by
  intro h
  have hx := (h ()).mpr trivial
  obtain ⟨meaning, found, law⟩ := hx.1 storage (by simp [impossible, model, design, Frontend.Design.lower])
  cases found
  exact law
