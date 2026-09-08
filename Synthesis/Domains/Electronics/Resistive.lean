import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.Resistive
set_option autoImplicit false

/-! # Resistive interconnection algebra

Closed forms for the standard resistive interconnections, with their monotonicity and
bounding properties. Series and parallel values are functions of the element parameters
only; they say nothing about a device outside its linear operating envelope.

Nondegeneracy hypotheses are explicit. A parallel combination needs a nonzero total,
and the divider identities need a nonzero loop resistance: an ideal source across a
zero-resistance loop has no operating point, and no theorem here supplies one. -/

variable {K : Type*}

section Field
variable [Field K]

/-- Parallel resistance `R₁ R₂ / (R₁ + R₂)`, the product-over-sum form. -/
def parallel (r s : K) : K := r * s / (r + s)

/-- Series resistance, recorded as a named operation for symmetry with `parallel`. -/
def series (r s : K) : K := r + s

theorem parallel_comm (r s : K) : parallel r s = parallel s r := by
  simp only [parallel]
  rw [mul_comm, add_comm]

theorem series_comm (r s : K) : series r s = series s r := add_comm r s

theorem series_assoc (r s t : K) : series (series r s) t = series r (series s t) :=
  add_assoc r s t

theorem parallel_zero (r : K) : parallel r 0 = 0 := by simp [parallel]

/-- Conductances add in parallel: the reciprocal form of the product-over-sum law. -/
theorem parallel_reciprocal {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    (parallel r s)⁻¹ = r⁻¹ + s⁻¹ := by
  simp only [parallel]
  field_simp
  ring

/-- Parallel combination is associative wherever every intermediate sum is nonzero. -/
theorem parallel_assoc {r s t : K} (hrs : r + s ≠ 0) (hst : s + t ≠ 0)
    (hleft : r * s + t * (r + s) ≠ 0) (hright : r * (s + t) + s * t ≠ 0) :
    parallel (parallel r s) t = parallel r (parallel s t) := by
  have left : parallel (parallel r s) t = r * s * t / (r * s + t * (r + s)) := by
    simp only [parallel]
    rw [div_mul_eq_mul_div, div_add' _ _ _ hrs, div_div_div_cancel_right₀ hrs]
  have right : parallel r (parallel s t) = r * (s * t) / (r * (s + t) + s * t) := by
    simp only [parallel]
    rw [mul_div_assoc', add_div' _ _ _ hst, div_div_div_cancel_right₀ hst]
  rw [left, right, div_eq_div_iff hleft hright]
  ring

/-- Equal resistances in parallel halve the resistance. -/
theorem parallel_self {r : K} (nonzero : r ≠ 0) (two : (2 : K) ≠ 0) : parallel r r = r / 2 := by
  simp only [parallel]
  rw [← two_mul]
  field_simp

/-! ## Dividers

The divider outputs are written as closed forms; `divider_kvl` shows that the two
branch voltages of a series pair reconstruct the source voltage exactly. -/

/-- Output of a two-resistor voltage divider measured across the second resistor. -/
def dividerVoltage (r s vin : K) : K := vin * s / (r + s)

/-- Current through the second branch of a two-resistor current divider. -/
def dividerCurrent (r s iin : K) : K := iin * r / (r + s)

theorem divider_kvl {r s vin : K} (loop : r + s ≠ 0) :
    dividerVoltage r s vin + dividerVoltage s r vin = vin := by
  have swapped : s + r ≠ 0 := by rwa [add_comm]
  simp only [dividerVoltage]
  field_simp
  ring

theorem divider_kcl {r s iin : K} (node : r + s ≠ 0) :
    dividerCurrent r s iin + dividerCurrent s r iin = iin := by
  have swapped : s + r ≠ 0 := by rwa [add_comm]
  simp only [dividerCurrent]
  field_simp
  ring

/-- The divider current is the loop current of the series pair: `i = v / (R₁ + R₂)`. -/
theorem divider_ohm (r s vin : K) : dividerVoltage r s vin = (vin / (r + s)) * s := by
  simp only [dividerVoltage]
  ring

/-! ## Wheatstone bridge -/

/-- Differential output of a bridge of two dividers sharing one source. -/
def bridge (r1 r2 r3 r4 vin : K) : K := dividerVoltage r1 r2 vin - dividerVoltage r3 r4 vin

/-- The bridge nulls exactly when the two arms have equal ratios. This is the balance
condition used for null measurements; it is independent of the excitation only under
the stated nondegeneracy of both arms. -/
theorem bridge_balanced_iff {r1 r2 r3 r4 vin : K}
    (left : r1 + r2 ≠ 0) (right : r3 + r4 ≠ 0) (excited : vin ≠ 0) :
    bridge r1 r2 r3 r4 vin = 0 ↔ r2 * (r3 + r4) = r4 * (r1 + r2) := by
  simp only [bridge, dividerVoltage, sub_eq_zero, div_eq_div_iff left right]
  constructor
  · intro h
    exact mul_left_cancel₀ excited (by linear_combination h)
  · intro h
    linear_combination vin * h

/-- A balanced bridge has equal arm products, the form used to solve for an unknown arm. -/
theorem bridge_balanced_products {r1 r2 r3 r4 : K}
    (balance : r2 * (r3 + r4) = r4 * (r1 + r2)) : r2 * r3 = r4 * r1 := by
  linear_combination balance

/-! ## Delta-wye transformation

The wye resistances below reproduce every terminal-pair resistance of the delta, which
is what makes the transformation admissible inside a larger network. -/

/-- Wye branch at the terminal opposite delta branch `a`. -/
def wyeBranch (a b c : K) : K := b * c / (a + b + c)

/-- Terminal-pair resistance of a delta between the two nodes joined by branch `c`:
`c` in parallel with the series path `a + b`. -/
def deltaTerminal (a b c : K) : K := parallel c (a + b)

/-- The delta and its wye equivalent present the same resistance at every terminal pair.
This is the transformation's defining property, proved here rather than assumed. -/
theorem delta_wye_terminal {a b c : K} (total : a + b + c ≠ 0) :
    wyeBranch a b c + wyeBranch b a c = deltaTerminal a b c := by
  have reordered : c + (a + b) ≠ 0 := by
    rw [show c + (a + b) = a + b + c by ring]
    exact total
  simp only [wyeBranch, deltaTerminal, parallel]
  rw [show b + a + c = a + b + c by ring]
  field_simp
  ring

theorem wye_branch_comm (a b c : K) : wyeBranch a b c = wyeBranch a c b := by
  simp only [wyeBranch]
  rw [mul_comm b c, show a + b + c = a + c + b by ring]

end Field

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem parallel_pos {r s : K} (hr : 0 < r) (hs : 0 < s) : 0 < parallel r s :=
  div_pos (mul_pos hr hs) (by linarith)

/-- A parallel path is strictly easier to drive than either branch alone. -/
theorem parallel_lt_left {r s : K} (hr : 0 < r) (hs : 0 < s) : parallel r s < r := by
  rw [parallel, div_lt_iff₀ (by linarith)]
  nlinarith

theorem parallel_lt_right {r s : K} (hr : 0 < r) (hs : 0 < s) : parallel r s < s := by
  rw [parallel_comm]
  exact parallel_lt_left hs hr

/-- A series path is at least as hard to drive as either branch alone. -/
theorem le_series_left {r s : K} (hs : 0 ≤ s) : r ≤ series r s := by
  simp only [series]
  linarith

theorem le_series_right {r s : K} (hr : 0 ≤ r) : s ≤ series r s := by
  simp only [series]
  linarith

/-- The parallel value never exceeds a quarter of the series value, with equality only
for matched branches. This is the arithmetic-harmonic mean inequality in circuit form. -/
theorem parallel_le_quarter_series {r s : K} (hr : 0 < r) (hs : 0 < s) :
    4 * parallel r s ≤ series r s := by
  have hsum : 0 < r + s := by linarith
  rw [series, parallel, ← mul_div_assoc, div_le_iff₀ hsum]
  nlinarith [sq_nonneg (r - s)]

/-- Monotonicity of the parallel law: increasing a branch resistance never lowers the
combination. -/
theorem parallel_mono_left {r r' s : K} (hr : 0 < r) (hr' : r ≤ r') (hs : 0 < s) :
    parallel r s ≤ parallel r' s := by
  have hr'pos : 0 < r' := lt_of_lt_of_le hr hr'
  rw [parallel, parallel, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hr' (mul_self_nonneg s)]

/-- A voltage divider driven by a nonnegative source never produces an output above the
source or below zero. This bounds the operating range of the divider. -/
theorem divider_bounds {r s vin : K} (hr : 0 ≤ r) (hs : 0 ≤ s) (hloop : 0 < r + s)
    (hin : 0 ≤ vin) : 0 ≤ dividerVoltage r s vin ∧ dividerVoltage r s vin ≤ vin := by
  constructor
  · exact div_nonneg (mul_nonneg hin hs) (le_of_lt hloop)
  · rw [dividerVoltage, div_le_iff₀ hloop]
    nlinarith

/-- Loading a divider with a larger lower resistance raises the output monotonically. -/
theorem divider_mono {r s s' vin : K} (hr : 0 < r) (hs : 0 ≤ s) (hss' : s ≤ s')
    (hin : 0 ≤ vin) : dividerVoltage r s vin ≤ dividerVoltage r s' vin := by
  have hs' : 0 ≤ s' := le_trans hs hss'
  rw [dividerVoltage, dividerVoltage, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg hin (le_of_lt hr)) (sub_nonneg.mpr hss')]

/-- Every wye branch of a delta with positive branches is positive, so the transformed
network stays inside the passive parameter envelope. -/
theorem wye_branch_pos {a b c : K} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < wyeBranch a b c :=
  div_pos (mul_pos hb hc) (by linarith)

end Ordered
end Synthesis.Domains.Electronics.Resistive
