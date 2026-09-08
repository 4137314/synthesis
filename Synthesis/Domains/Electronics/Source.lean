import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Synthesis.Domains.Electronics.Element

namespace Synthesis.Domains.Electronics.Source
set_option autoImplicit false

/-! # Driving-point behaviour of a linear source

A Thévenin source `v = E - R i` loaded by a resistance `R_L` has exactly one operating
point whenever the loop resistance is nonzero. This module solves that circuit and
proves the standard consequences: the load line, the power split between the internal
and external resistances, the maximum power transfer bound and the efficiency at match.

The internal resistance is a model parameter of the equivalent source. Reproducing the
terminal behaviour of a device does not license any claim about its internal
temperature, its safe operating area or the physical location of its dissipation. -/

variable {K : Type*}

section Field
variable [Field K]

/-- Loop current of a Thévenin source with electromotive force `e` and internal
resistance `r` driving a load resistance `load`. -/
def loadCurrent (e r load : K) : K := e / (r + load)

/-- Terminal voltage across the load at the operating point. -/
def loadVoltage (e r load : K) : K := e * load / (r + load)

/-- Power absorbed by the load. -/
def loadPower (e r load : K) : K := e ^ 2 * load / (r + load) ^ 2

/-- Power delivered by the ideal source, including the internal dissipation. -/
def sourcePower (e r load : K) : K := e ^ 2 / (r + load)

/-- The operating point exists and is unique for every nonzero loop resistance: it is
the intersection of the source line `v = e - r i` with the load line `v = load * i`. -/
theorem operating_point_unique {e r load : K} (loop : r + load ≠ 0) :
    ∃ i : K, e - r * i = load * i ∧ ∀ j : K, e - r * j = load * j → j = i := by
  refine ⟨loadCurrent e r load, ?_, ?_⟩
  · rw [loadCurrent]
    field_simp
    ring
  · intro j hj
    rw [loadCurrent, eq_div_iff loop]
    linear_combination -hj

/-- Ohm's law holds at the terminals: the load voltage is the loop current times the
load resistance. -/
theorem load_ohm (e r load : K) : loadVoltage e r load = loadCurrent e r load * load := by
  simp only [loadVoltage, loadCurrent]
  ring

/-- The load power is the product of the terminal variables. -/
theorem load_power_terminal {e r load : K} (loop : r + load ≠ 0) :
    loadPower e r load = loadVoltage e r load * loadCurrent e r load := by
  simp only [loadPower, loadVoltage, loadCurrent]
  field_simp

/-- Conservation of energy in the equivalent source: what the ideal source delivers is
split between the internal resistance and the load. -/
theorem power_split {e r load : K} (loop : r + load ≠ 0) :
    sourcePower e r load = loadCurrent e r load ^ 2 * r + loadPower e r load := by
  simp only [sourcePower, loadCurrent, loadPower]
  field_simp

/-- Short-circuit current and open-circuit voltage of the equivalent source. -/
theorem short_circuit_current (e r : K) : loadCurrent e r 0 = e / r := by
  simp [loadCurrent]

theorem open_circuit_no_current {e r load : K} (loop : r + load ≠ 0) :
    loadCurrent e r load = 0 ↔ e = 0 := by
  simp [loadCurrent, div_eq_zero_iff, loop]

/-- Source identification: the internal resistance is recovered from the open-circuit
voltage and the short-circuit current, which is how a Thévenin equivalent is measured. -/
theorem internal_resistance_from_measurements {e r : K} (internal : r ≠ 0) (source : e ≠ 0) :
    e / loadCurrent e r 0 = r := by
  rw [short_circuit_current]
  field_simp

/-- Superposition for two independent sources in the same loop: the loop current is the
sum of the currents each source drives alone. -/
theorem superposition {e f r load : K} (loop : r + load ≠ 0) :
    loadCurrent (e + f) r load = loadCurrent e r load + loadCurrent f r load := by
  simp only [loadCurrent]
  field_simp

theorem homogeneity {a e r load : K} : loadCurrent (a * e) r load = a * loadCurrent e r load := by
  simp only [loadCurrent]
  ring

end Field

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem load_power_nonneg {e r load : K} (external : 0 ≤ load) :
    0 ≤ loadPower e r load :=
  div_nonneg (mul_nonneg (sq_nonneg e) external) (sq_nonneg _)

/-- **Maximum power transfer**. A source with positive internal resistance can never
deliver more than `E² / (4 R)` to a resistive load, whatever the load value. -/
theorem maximum_power_transfer {e r load : K} (internal : 0 < r) (external : 0 ≤ load) :
    loadPower e r load ≤ e ^ 2 / (4 * r) := by
  have loop : 0 < r + load := by linarith
  have square : 0 < (r + load) ^ 2 := by positivity
  rw [loadPower, div_le_div_iff₀ square (by linarith)]
  nlinarith [sq_nonneg (r - load), sq_nonneg e, mul_nonneg (sq_nonneg e) (sq_nonneg (r - load))]

/-- The bound is attained exactly at the matched load, so it is tight. -/
theorem matched_load_power {e r : K} (internal : 0 < r) :
    loadPower e r r = e ^ 2 / (4 * r) := by
  have nonzero : r ≠ 0 := ne_of_gt internal
  simp only [loadPower]
  rw [show r + r = 2 * r by ring]
  field_simp
  ring

/-- Efficiency of power transfer: the fraction of the delivered power that reaches the
load. It is the load fraction of the loop resistance. -/
def efficiency (r load : K) : K := load / (r + load)

theorem efficiency_eq_power_ratio {e r load : K} (internal : 0 < r) (external : 0 ≤ load)
    (source : e ≠ 0) : loadPower e r load = efficiency r load * sourcePower e r load := by
  have loop : r + load ≠ 0 := by positivity
  simp only [loadPower, efficiency, sourcePower]
  field_simp

/-- At the matched load the efficiency is one half: maximum power transfer is not
maximum efficiency. This is the standard design trade-off, proved rather than asserted. -/
theorem matched_efficiency {r : K} (internal : 0 < r) : efficiency r r = 1 / 2 := by
  have nonzero : r + r ≠ 0 := by positivity
  simp only [efficiency]
  rw [show r + r = 2 * r by ring]
  field_simp

theorem efficiency_le_one {r load : K} (internal : 0 < r) (external : 0 ≤ load) :
    efficiency r load ≤ 1 := by
  have loop : 0 < r + load := by linarith
  rw [efficiency, div_le_one loop]
  linarith

/-- Efficiency increases with the load resistance: lightly loaded sources waste less. -/
theorem efficiency_mono {r load load' : K} (internal : 0 < r) (external : 0 ≤ load)
    (heavier : load ≤ load') : efficiency r load ≤ efficiency r load' := by
  have loop : 0 < r + load := by linarith
  have loop' : 0 < r + load' := by linarith
  rw [efficiency, efficiency, div_le_div_iff₀ loop loop']
  nlinarith

/-- A dead Thévenin source only absorbs power: with no electromotive force it is an
ordinary resistor, whatever the load. -/
theorem dead_source_absorbs {r v i : K} (internal : 0 ≤ r)
    (point : (Element.TwoTerminal.thevenin 0 r).Admissible v i) :
    Element.TwoTerminal.delivered v i ≤ 0 := by
  rw [Element.TwoTerminal.delivered, show v = 0 - r * i from point]
  nlinarith [mul_self_nonneg i]

/-- A live Thévenin source has an operating point at which it delivers strictly positive
power, so it cannot be modelled as a passive element. Together with `dead_source_absorbs`
this separates sources from resistors by their terminal behaviour alone. -/
theorem live_source_delivers {e r : K} (internal : 0 < r) (live : e ≠ 0) :
    ∃ v i : K, (Element.TwoTerminal.thevenin e r).Admissible v i ∧
      0 < Element.TwoTerminal.delivered v i := by
  have hr : r ≠ 0 := ne_of_gt internal
  refine ⟨e - r * (e / (2 * r)), e / (2 * r), rfl, ?_⟩
  have halved : e - r * (e / (2 * r)) = e / 2 := by
    field_simp
    ring
  rw [Element.TwoTerminal.delivered, halved]
  have square : 0 < e * e := by
    rcases lt_or_gt_of_ne live with he | he
    · exact mul_pos_of_neg_of_neg he he
    · exact mul_pos he he
  have expand : e / 2 * (e / (2 * r)) = e * e / (4 * r) := by
    field_simp
    ring
  rw [expand]
  positivity

end Ordered
end Synthesis.Domains.Electronics.Source
