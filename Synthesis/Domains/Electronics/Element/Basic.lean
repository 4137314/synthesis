import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.Element
set_option autoImplicit false

/-! # Two-terminal elements as admissible operating sets

This module holds the representation and the elementary catalog. Interconnection is in
`Synthesis.Domains.Electronics.Element.Interconnect` and passivity in
`Synthesis.Domains.Electronics.Element.Passivity`.

A two-terminal element is modelled by the set of terminal pairs `(v, i)` it admits at a
fixed operating point. This relational view covers ideal sources, which are not
functions of their terminal variables, and it makes series and parallel interconnection
definable without solving a circuit.

The scalar field is arbitrary: instantiating at `ℚ` keeps the exact rational semantics
of `Synthesis.Domains.Electronics`, and instantiating at `ℝ` matches the analytic layer.
Every element here is memoryless; reactive elements need the time-domain model in
`Synthesis.Domains.Electronics.Storage`.

Sign convention: `v` is the drop from the first to the second terminal and `i` enters
the first terminal, so `v * i` is the power absorbed by the element. -/

variable {K : Type*}

/-- The admissible terminal pairs of a two-terminal element. Membership is the only
claim; realizability of an operating point is a separate obligation. -/
structure TwoTerminal (K : Type*) where
  Admissible : K → K → Prop

namespace TwoTerminal

/-- Two elements are equivalent when no terminal measurement distinguishes them. -/
def Equivalent (a b : TwoTerminal K) : Prop := ∀ v i, a.Admissible v i ↔ b.Admissible v i

theorem equivalent_refl (a : TwoTerminal K) : Equivalent a a := fun _ _ => Iff.rfl

theorem equivalent_symm {a b : TwoTerminal K} (h : Equivalent a b) : Equivalent b a :=
  fun v i => (h v i).symm

theorem equivalent_trans {a b c : TwoTerminal K}
    (hab : Equivalent a b) (hbc : Equivalent b c) : Equivalent a c :=
  fun v i => (hab v i).trans (hbc v i)

section Algebraic
variable [Field K]

/-- Absorbed power at an operating point, in the passive sign convention. -/
def absorbed (v i : K) : K := v * i

/-- Feasibility: at least one admissible operating point exists. An element with an
empty admissible set satisfies every guarantee vacuously, so certificates must exclude it. -/
def Feasible (a : TwoTerminal K) : Prop := ∃ v i, a.Admissible v i

/-! ## The elementary catalog -/

/-- Ideal linear resistor `v = R i`. -/
def resistor (r : K) : TwoTerminal K := ⟨fun v i => v = r * i⟩

/-- Ideal linear conductor `i = G v`, the dual parameterization. -/
def conductor (g : K) : TwoTerminal K := ⟨fun v i => i = g * v⟩

/-- Ideal independent voltage source: the terminal voltage is fixed for every current. -/
def voltageSource (e : K) : TwoTerminal K := ⟨fun v _ => v = e⟩

/-- Ideal independent current source: the branch current is fixed for every voltage. -/
def currentSource (s : K) : TwoTerminal K := ⟨fun _ i => i = s⟩

/-- An open circuit carries no current at any voltage. -/
def openCircuit : TwoTerminal K := ⟨fun _ i => i = 0⟩

/-- A short circuit holds zero voltage at any current. -/
def shortCircuit : TwoTerminal K := ⟨fun v _ => v = 0⟩

/-- A Thévenin source: an ideal voltage source behind a series resistance. Both source
models below use the *active* orientation, in which the reference current leaves the
positive terminal, so `v * i` is the power they deliver rather than absorb. -/
def thevenin (e r : K) : TwoTerminal K := ⟨fun v i => v = e - r * i⟩

/-- A Norton source: an ideal current source across a parallel conductance, in the same
active orientation as `thevenin`. -/
def norton (s g : K) : TwoTerminal K := ⟨fun v i => i = s - g * v⟩

/-- Power delivered by an element in the active orientation. It is the negation of
`absorbed`, and the two must not be mixed within one element. -/
def delivered (v i : K) : K := v * i

theorem resistor_feasible (r : K) : Feasible (resistor r) := ⟨r * 1, 1, rfl⟩

theorem conductor_feasible (g : K) : Feasible (conductor g) := ⟨1, g * 1, rfl⟩

theorem voltage_source_feasible (e : K) : Feasible (voltageSource e) := ⟨e, 0, rfl⟩

theorem current_source_feasible (s : K) : Feasible (currentSource s) := ⟨0, s, rfl⟩

theorem open_feasible : Feasible (openCircuit (K := K)) := ⟨0, 0, rfl⟩

theorem short_feasible : Feasible (shortCircuit (K := K)) := ⟨0, 0, rfl⟩

theorem thevenin_feasible (e r : K) : Feasible (thevenin e r) := ⟨e - r * 0, 0, rfl⟩

/-! ## Degenerate and dual parameterizations -/

theorem resistor_zero_short : Equivalent (resistor (0 : K)) shortCircuit := by
  intro v i
  simp [resistor, shortCircuit]

theorem conductor_zero_open : Equivalent (conductor (0 : K)) openCircuit := by
  intro v i
  simp [conductor, openCircuit]

/-- The two linear parameterizations agree away from the degenerate cases: an ideal
short has no finite conductance and an ideal open has no finite resistance. -/
theorem resistor_conductor_dual {r : K} (nonzero : r ≠ 0) :
    Equivalent (resistor r) (conductor r⁻¹) := by
  intro v i
  simp only [resistor, conductor]
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- A Thévenin source with zero internal resistance is an ideal voltage source. -/
theorem thevenin_zero (e : K) : Equivalent (thevenin e 0) (voltageSource e) := by
  intro v i
  simp [thevenin, voltageSource]

/-- Thévenin and Norton forms of the same nondegenerate source are indistinguishable at
the terminals. The equivalence fails for an ideal source without internal resistance. -/
theorem thevenin_norton {e r : K} (nonzero : r ≠ 0) :
    Equivalent (thevenin e r) (norton (e / r) r⁻¹) := by
  intro v i
  simp only [thevenin, norton]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have expand : r * i = e - v := by
      rw [h]
      field_simp
    linear_combination expand

end Algebraic
end TwoTerminal
end Synthesis.Domains.Electronics.Element
