import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Synthesis.Domains.Electronics.Digital
set_option autoImplicit false

/-! # Logic gates and static logic levels

Two separate models. The first is the Boolean function computed by a gate, where a
complete case analysis decides every identity, including the universality of `nand`.
The second is the static electrical discipline that lets a continuous voltage stand for
a Boolean value: threshold levels, noise margins and the guarantee that a restored
output survives bounded interference.

Neither model has time in it. Propagation delay, transition time, dynamic power,
metastability and race conditions are outside them, and no theorem here establishes
that a physical gate network settles or is free of hazards. -/

/-! ## Boolean gate identities -/

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

/-! ## Static logic levels

A voltage represents a Boolean value only through a discipline of thresholds. The
guarantee below is the reason digital logic composes: an output driven to a valid level
is still read correctly after bounded interference. -/

/-- A static logic level discipline: input thresholds and guaranteed output levels. -/
structure Discipline where
  inputLowMax : ℝ
  inputHighMin : ℝ
  outputLowMax : ℝ
  outputHighMin : ℝ
  separated : inputLowMax < inputHighMin
  lowRestoring : outputLowMax ≤ inputLowMax
  highRestoring : inputHighMin ≤ outputHighMin

namespace Discipline

/-- Low-level noise margin. -/
def marginLow (d : Discipline) : ℝ := d.inputLowMax - d.outputLowMax

/-- High-level noise margin. -/
def marginHigh (d : Discipline) : ℝ := d.outputHighMin - d.inputHighMin

theorem marginLow_nonneg (d : Discipline) : 0 ≤ d.marginLow := by
  have := d.lowRestoring
  simp only [marginLow]
  linarith

theorem marginHigh_nonneg (d : Discipline) : 0 ≤ d.marginHigh := by
  have := d.highRestoring
  simp only [marginHigh]
  linarith

/-- Interpretation of a voltage as a Boolean value. Voltages inside the forbidden band
have no interpretation; this is a refusal to guess, not a third logic value. -/
noncomputable def interpret (d : Discipline) (v : ℝ) : Option Bool :=
  if v ≤ d.inputLowMax then some false
  else if d.inputHighMin ≤ v then some true
  else none

/-- No voltage is read as both values: the thresholds are unambiguous. -/
theorem interpret_unambiguous (d : Discipline) (v : ℝ) :
    ¬(d.interpret v = some false ∧ d.interpret v = some true) := by
  rintro ⟨low, high⟩
  rw [low] at high
  exact Bool.false_ne_true (Option.some.inj high)

/-- A voltage in the forbidden band has no interpretation. -/
theorem interpret_forbidden (d : Discipline) {v : ℝ}
    (above : d.inputLowMax < v) (below : v < d.inputHighMin) : d.interpret v = none := by
  simp only [interpret]
  rw [if_neg (not_le.mpr above), if_neg (not_le.mpr below)]

/-- **Level restoration**: a valid driven low is read as `false`. -/
theorem interpret_driven_low (d : Discipline) {v : ℝ} (driven : v ≤ d.outputLowMax) :
    d.interpret v = some false := by
  have := d.lowRestoring
  simp only [interpret]
  rw [if_pos (by linarith)]

/-- **Level restoration**: a valid driven high is read as `true`. -/
theorem interpret_driven_high (d : Discipline) {v : ℝ} (driven : d.outputHighMin ≤ v) :
    d.interpret v = some true := by
  have separation := d.separated
  have restoring := d.highRestoring
  simp only [interpret]
  rw [if_neg (by push Not; linarith), if_pos (by linarith)]

/-- **Noise immunity**: interference bounded by the noise margin cannot change the value
read from a driven low output. -/
theorem noise_immunity_low (d : Discipline) {v noise : ℝ} (driven : v ≤ d.outputLowMax)
    (bounded : |noise| ≤ d.marginLow) : d.interpret (v + noise) = some false := by
  have bound : noise ≤ d.marginLow := le_trans (le_abs_self noise) bounded
  have margin : d.marginLow = d.inputLowMax - d.outputLowMax := rfl
  simp only [interpret]
  rw [if_pos (by rw [margin] at bound; linarith)]

/-- **Noise immunity**: interference bounded by the noise margin cannot change the value
read from a driven high output. -/
theorem noise_immunity_high (d : Discipline) {v noise : ℝ} (driven : d.outputHighMin ≤ v)
    (bounded : |noise| ≤ d.marginHigh) : d.interpret (v + noise) = some true := by
  have bound : -noise ≤ d.marginHigh := le_trans (neg_le_abs noise) bounded
  have margin : d.marginHigh = d.outputHighMin - d.inputHighMin := rfl
  have separation := d.separated
  rw [margin] at bound
  simp only [interpret]
  rw [if_neg (by push Not; linarith), if_pos (by linarith)]

end Discipline

/-! ## Complementary switching

An ideal complementary pair with non-overlapping thresholds never conducts from supply
to ground, which is the static-power argument for complementary logic. -/

/-- Ideal threshold model of a complementary inverter. -/
structure Complementary where
  supply : ℝ
  pullDownThreshold : ℝ
  pullUpThreshold : ℝ
  supplyPositive : 0 < supply

namespace Complementary

/-- The pull-down device conducts above its threshold. -/
def pullDownConducting (c : Complementary) (input : ℝ) : Prop := c.pullDownThreshold < input

/-- The pull-up device conducts below the complementary threshold. -/
def pullUpConducting (c : Complementary) (input : ℝ) : Prop :=
  input < c.supply - c.pullUpThreshold

/-- **No crowbar path**: when the thresholds do not overlap, no input voltage turns both
devices on, so the ideal static gate draws no supply current. -/
theorem no_static_path (c : Complementary)
    (nonOverlapping : c.supply - c.pullUpThreshold ≤ c.pullDownThreshold) (input : ℝ) :
    ¬(c.pullDownConducting input ∧ c.pullUpConducting input) := by
  rintro ⟨down, up⟩
  simp only [pullDownConducting, pullUpConducting] at down up
  linarith

/-- Outside the transition window exactly one device conducts, so the output is driven. -/
theorem low_input_pulls_up (c : Complementary) {input : ℝ}
    (low : input < c.supply - c.pullUpThreshold)
    (belowThreshold : input ≤ c.pullDownThreshold) :
    c.pullUpConducting input ∧ ¬c.pullDownConducting input := by
  refine ⟨low, ?_⟩
  simp only [pullDownConducting]
  linarith

theorem high_input_pulls_down (c : Complementary) {input : ℝ}
    (high : c.pullDownThreshold < input)
    (aboveThreshold : c.supply - c.pullUpThreshold ≤ input) :
    c.pullDownConducting input ∧ ¬c.pullUpConducting input := by
  refine ⟨high, ?_⟩
  simp only [pullUpConducting]
  linarith

end Complementary
end Synthesis.Domains.Electronics.Digital
