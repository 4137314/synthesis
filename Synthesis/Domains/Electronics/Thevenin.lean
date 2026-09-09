import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Synthesis.Domains.Electronics.Element

namespace Synthesis.Domains.Electronics.Thevenin
set_option autoImplicit false

/-! # Thévenin equivalence of a one-port

An affine one-port is an element whose admissible pairs satisfy `v = e + r i`. The family
contains the ideal voltage source (`r = 0`), the ideal resistor (`e = 0`) and every
Thévenin or Norton source, and this module proves the three facts that make it the right
notion of "linear one-port":

* **Closure.** The family is closed under series and parallel interconnection, with the
  familiar combination laws for the equivalent electromotive force and the equivalent
  resistance. Any network of independent voltage sources and resistances assembled by
  those two operations therefore presents an affine driving point.
* **Uniqueness.** Two affine one-ports that no terminal measurement can distinguish have
  the same parameters, so "the" Thévenin equivalent is well defined. This is the step
  usually left implicit, and it is what licenses identifying a source by measuring its
  open-circuit voltage and its slope.
* **Separation.** An affine one-port is passive exactly when it is a plain resistor with
  nonnegative resistance. A nonzero electromotive force always has an operating point at
  which the element delivers energy.

Everything is at a fixed operating point and in the passive sign convention throughout,
so the internal resistance below is the *terminal* slope. Reproducing a driving-point
relation licenses no claim about where inside a real device the dissipation occurs, and
the closure results say nothing about networks assembled by anything other than series
and parallel composition: a bridge is not covered. -/

open Element Element.TwoTerminal

variable {K : Type*}

section Field
variable [Field K]

/-- An affine one-port `v = e + r i`, in the passive sign convention. -/
def affine (e r : K) : TwoTerminal K := ⟨fun v i => v = e + r * i⟩

theorem affine_feasible (e r : K) : Feasible (affine e r) := ⟨e + r * 0, 0, rfl⟩

/-- With no electromotive force an affine one-port is an ideal resistor. -/
theorem affine_resistor (r : K) : Equivalent (affine 0 r) (resistor r) := by
  intro v i
  simp [affine, resistor]

/-- With no internal resistance it is an ideal voltage source. -/
theorem affine_voltageSource (e : K) : Equivalent (affine e 0) (voltageSource e) := by
  intro v i
  simp [affine, voltageSource]

/-- The Thévenin element of the catalog is affine after the change of orientation: its
reference current leaves the positive terminal, which flips the sign of the slope. -/
theorem affine_thevenin (e r : K) : Equivalent (affine e (-r)) (thevenin e r) := by
  intro v i
  simp only [affine, thevenin]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [h]
    ring

/-- Away from a short circuit the affine one-port has the Norton current form. -/
theorem affine_norton {e r : K} (internal : r ≠ 0) :
    Equivalent (affine e r) ⟨fun v i => i = (v - e) / r⟩ := by
  intro v i
  simp only [affine]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-! ## Closure under interconnection -/

/-- **Series composition of affine one-ports.** Electromotive forces and internal
resistances both add, which is Kirchhoff's voltage law at a shared branch current. -/
theorem affine_series (e r f s : K) :
    Equivalent (series (affine e r) (affine f s)) (affine (e + f) (r + s)) := by
  intro v i
  simp only [series, affine]
  constructor
  · rintro ⟨va, vb, ha, hb, hv⟩
    rw [hv, ha, hb]
    ring
  · intro h
    exact ⟨e + r * i, f + s * i, rfl, rfl, by rw [h]; ring⟩

/-- **Parallel composition of affine one-ports.** The equivalent resistance is the
product over sum and the equivalent electromotive force is the conductance-weighted
average, which is Millman's form of the Thévenin equivalent of two branches. Both source
branches must have a nonzero internal resistance: two ideal voltage sources in parallel
are an inconsistent, not a combinable, interconnection. -/
theorem affine_parallel {e r f s : K} (first : r ≠ 0) (second : s ≠ 0) (node : r + s ≠ 0) :
    Equivalent (parallel (affine e r) (affine f s))
      (affine ((e * s + f * r) / (r + s)) (r * s / (r + s))) := by
  intro v i
  simp only [parallel, affine]
  constructor
  · rintro ⟨ia, ib, ha, hb, hi⟩
    field_simp
    linear_combination s * ha + r * hb - r * s * hi
  · intro h
    have cleared : v * (r + s) = e * s + f * r + r * s * i := by
      rw [h]
      field_simp
    refine ⟨(v - e) / r, (v - f) / s, by field_simp; ring, by field_simp; ring, ?_⟩
    field_simp
    linear_combination -cleared

/-! ## Uniqueness of the equivalent -/

/-- The open-circuit voltage of an affine one-port is its electromotive force. -/
theorem affine_open_circuit (e r : K) : (affine e r).Admissible e 0 := by
  simp [affine]

/-- The terminal slope of an affine one-port is its internal resistance. -/
theorem affine_unit_current (e r : K) : (affine e r).Admissible (e + r) 1 := by
  simp [affine]

/-- **Uniqueness of the Thévenin equivalent.** Two affine one-ports that no terminal
measurement distinguishes have the same electromotive force and the same internal
resistance. The equivalent is therefore determined by the open-circuit voltage and the
terminal slope, which is exactly how it is measured. -/
theorem affine_unique {e r f s : K} (indistinguishable : Equivalent (affine e r) (affine f s)) :
    e = f ∧ r = s := by
  have open_circuit : e = f + s * 0 := (indistinguishable e 0).mp (affine_open_circuit e r)
  have loaded : e + r = f + s * 1 := (indistinguishable (e + r) 1).mp (affine_unit_current e r)
  rw [mul_zero, add_zero] at open_circuit
  rw [mul_one] at loaded
  exact ⟨open_circuit, by linear_combination loaded - open_circuit⟩

/-- Identification from two measurements: an affine one-port is fixed by its open-circuit
voltage and by one loaded operating point at a nonzero current. -/
theorem affine_identified {e r : K} {v i : K} (flowing : i ≠ 0)
    (measured : (affine e r).Admissible v i) : r = (v - e) / i := by
  simp only [affine] at measured
  rw [eq_div_iff flowing]
  linear_combination -measured

end Field

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Passivity separates sources from resistances.** An affine one-port absorbs
nonnegative power at every admissible operating point exactly when its electromotive
force vanishes and its internal resistance is nonnegative, that is, exactly when it is an
ordinary resistor. A live source always has an operating point at which it delivers. -/
theorem affine_passive_iff {e r : K} : Passive (affine e r) ↔ e = 0 ∧ 0 ≤ r := by
  constructor
  · intro passive
    have resistive : 0 ≤ r := by
      have forward := passive (e + r * 1) 1 rfl
      have backward := passive (e + r * (-1)) (-1) rfl
      simp only [absorbed] at forward backward
      nlinarith
    refine ⟨?_, resistive⟩
    by_contra live
    have square : 0 < e * e := by
      rcases lt_or_gt_of_ne live with negative | positive
      · exact mul_pos_of_neg_of_neg negative negative
      · exact mul_pos positive positive
    have denominator : (0 : K) < 2 * (r + 1) := by linarith
    have small : (0 : K) < 1 / (2 * (r + 1)) := by positivity
    have bounded : r * (1 / (2 * (r + 1))) < 1 := by
      rw [mul_one_div, div_lt_one denominator]
      linarith
    have witness := passive (e + r * (-e * (1 / (2 * (r + 1))))) (-e * (1 / (2 * (r + 1)))) rfl
    simp only [absorbed] at witness
    have delivering : 0 < e * e * (1 / (2 * (r + 1))) * (1 - r * (1 / (2 * (r + 1)))) :=
      mul_pos (mul_pos square small) (by linarith)
    nlinarith [witness, delivering]
  · rintro ⟨dead, resistive⟩
    intro v i point
    simp only [affine, dead, zero_add] at point
    simp only [absorbed]
    rw [point]
    nlinarith [mul_self_nonneg i]

/-- A live affine one-port delivers strictly positive power at some operating point, so it
cannot be modelled as a passive element whatever its internal resistance. -/
theorem affine_not_passive {e r : K} (live : e ≠ 0) : ¬Passive (affine e r) := by
  intro passive
  exact live (affine_passive_iff.mp passive).1

end Ordered
end Synthesis.Domains.Electronics.Thevenin
