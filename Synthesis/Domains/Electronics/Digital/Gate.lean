import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Synthesis.Domains.Electronics.Digital
set_option autoImplicit false

/-! # Boolean gate identities

The function a gate computes, with no electrical or temporal content. A complete case
analysis decides every identity here, including the functional completeness of `nand`
for this catalog and the arithmetic correctness of the full adder.

Propagation delay, transition time, dynamic power, metastability, races and hazards are
not modelled; the electrical discipline that lets a voltage stand for a Boolean value is
in `Synthesis.Domains.Electronics.Digital.Level`. -/


def nand (a b : Bool) : Bool := !(a && b)

def nor (a b : Bool) : Bool := !(a || b)

def implication (a b : Bool) : Bool := !a || b

def majority (a b c : Bool) : Bool := (a && b) || (b && c) || (a && c)

def multiplexer (select a b : Bool) : Bool := (!select && a) || (select && b)

/-- A full adder as sum and carry outputs. -/
def fullAdder (a b carry : Bool) : Bool × Bool :=
  (xor (xor a b) carry, majority a b carry)

theorem nand_not (a : Bool) : nand a a = !a := by decide +revert

theorem nand_and (a b : Bool) : nand (nand a b) (nand a b) = (a && b) := by decide +revert

theorem nand_or (a b : Bool) : nand (nand a a) (nand b b) = (a || b) := by decide +revert

/-- `nand` is functionally complete for this catalog: negation, conjunction, disjunction
and implication are all built from it alone. -/
theorem nand_implication (a b : Bool) : nand a (nand b b) = implication a b := by decide +revert

theorem nor_not (a : Bool) : nor a a = !a := by decide +revert

theorem nor_or (a b : Bool) : nor (nor a b) (nor a b) = (a || b) := by decide +revert

theorem de_morgan_and (a b : Bool) : !(a && b) = (!a || !b) := by decide +revert

theorem de_morgan_or (a b : Bool) : !(a || b) = (!a && !b) := by decide +revert

theorem multiplexer_low (a b : Bool) : multiplexer false a b = a := by decide +revert

theorem multiplexer_high (a b : Bool) : multiplexer true a b = b := by decide +revert

theorem majority_comm (a b c : Bool) : majority a b c = majority b a c := by decide +revert

theorem majority_idempotent (a : Bool) : majority a a a = a := by decide +revert

/-- The full adder computes the two-bit sum of its three inputs, with the carry as the
high bit. This is the arithmetic specification, not a restatement of the circuit. -/
theorem fullAdder_correct (a b carry : Bool) :
    (if (fullAdder a b carry).2 then 2 else 0) + (if (fullAdder a b carry).1 then 1 else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) + (if carry then 1 else 0) := by
  decide +revert
end Synthesis.Domains.Electronics.Digital
