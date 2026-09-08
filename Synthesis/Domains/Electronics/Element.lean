import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.Element
set_option autoImplicit false

/-! # Two-terminal elements as admissible operating sets

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

/-! ## Interconnection

Series and parallel composition are defined by their Kirchhoff constraints: a series
pair shares the branch current and adds voltages, a parallel pair shares the terminal
voltage and adds currents. -/

/-- Series interconnection: shared current, added voltages. -/
def series (a b : TwoTerminal K) : TwoTerminal K :=
  ⟨fun v i => ∃ va vb, a.Admissible va i ∧ b.Admissible vb i ∧ v = va + vb⟩

/-- Parallel interconnection: shared voltage, added currents. -/
def parallel (a b : TwoTerminal K) : TwoTerminal K :=
  ⟨fun v i => ∃ ia ib, a.Admissible v ia ∧ b.Admissible v ib ∧ i = ia + ib⟩

theorem series_comm (a b : TwoTerminal K) : Equivalent (series a b) (series b a) := by
  intro v i
  constructor
  · rintro ⟨va, vb, ha, hb, hv⟩
    exact ⟨vb, va, hb, ha, by rw [hv]; ring⟩
  · rintro ⟨vb, va, hb, ha, hv⟩
    exact ⟨va, vb, ha, hb, by rw [hv]; ring⟩

theorem parallel_comm (a b : TwoTerminal K) : Equivalent (parallel a b) (parallel b a) := by
  intro v i
  constructor
  · rintro ⟨ia, ib, ha, hb, hi⟩
    exact ⟨ib, ia, hb, ha, by rw [hi]; ring⟩
  · rintro ⟨ib, ia, hb, ha, hi⟩
    exact ⟨ia, ib, ha, hb, by rw [hi]; ring⟩

theorem series_assoc (a b c : TwoTerminal K) :
    Equivalent (series (series a b) c) (series a (series b c)) := by
  intro v i
  constructor
  · rintro ⟨vab, vc, ⟨va, vb, ha, hb, hvab⟩, hc, hv⟩
    exact ⟨va, vb + vc, ha, ⟨vb, vc, hb, hc, rfl⟩, by rw [hv, hvab]; ring⟩
  · rintro ⟨va, vbc, ha, ⟨vb, vc, hb, hc, hvbc⟩, hv⟩
    exact ⟨va + vb, vc, ⟨va, vb, ha, hb, rfl⟩, hc, by rw [hv, hvbc]; ring⟩

theorem parallel_assoc (a b c : TwoTerminal K) :
    Equivalent (parallel (parallel a b) c) (parallel a (parallel b c)) := by
  intro v i
  constructor
  · rintro ⟨iab, ic, ⟨ia, ib, ha, hb, hiab⟩, hc, hi⟩
    exact ⟨ia, ib + ic, ha, ⟨ib, ic, hb, hc, rfl⟩, by rw [hi, hiab]; ring⟩
  · rintro ⟨ia, ibc, ha, ⟨ib, ic, hb, hc, hibc⟩, hi⟩
    exact ⟨ia + ib, ic, ⟨ia, ib, ha, hb, rfl⟩, hc, by rw [hi, hibc]; ring⟩

/-- Kirchhoff's voltage law makes series resistances add. -/
theorem series_resistor (r s : K) :
    Equivalent (series (resistor r) (resistor s)) (resistor (r + s)) := by
  intro v i
  constructor
  · rintro ⟨va, vb, ha, hb, hv⟩
    simp only [resistor] at ha hb ⊢
    rw [hv, ha, hb]
    ring
  · intro h
    exact ⟨r * i, s * i, rfl, rfl, by rw [show v = (r + s) * i from h]; ring⟩

/-- Kirchhoff's current law makes parallel conductances add. -/
theorem parallel_conductor (g h : K) :
    Equivalent (parallel (conductor g) (conductor h)) (conductor (g + h)) := by
  intro v i
  constructor
  · rintro ⟨ia, ib, ha, hb, hi⟩
    simp only [conductor] at ha hb ⊢
    rw [hi, ha, hb]
    ring
  · intro hgh
    exact ⟨g * v, h * v, rfl, rfl, by rw [show i = (g + h) * v from hgh]; ring⟩

/-- A series short circuit is transparent, and a parallel open circuit is invisible.
These are the neutral elements of the two interconnections. -/
theorem series_short (a : TwoTerminal K) : Equivalent (series a shortCircuit) a := by
  intro v i
  constructor
  · rintro ⟨va, vb, ha, hb, hv⟩
    rw [show v = va from by rw [hv, show vb = 0 from hb, add_zero]]
    exact ha
  · intro ha
    exact ⟨v, 0, ha, rfl, by ring⟩

theorem parallel_open (a : TwoTerminal K) : Equivalent (parallel a openCircuit) a := by
  intro v i
  constructor
  · rintro ⟨ia, ib, ha, hb, hi⟩
    rw [show i = ia from by rw [hi, show ib = 0 from hb, add_zero]]
    exact ha
  · intro ha
    exact ⟨i, 0, ha, rfl, by ring⟩

/-- An ideal current source in series forces the branch current. -/
theorem series_current_source (a : TwoTerminal K) (s v i : K) :
    (series a (currentSource s)).Admissible v i → i = s := by
  rintro ⟨_, _, _, hb, _⟩
  exact hb

/-- An ideal voltage source in parallel forces the terminal voltage. -/
theorem parallel_voltage_source (a : TwoTerminal K) (e v i : K) :
    (parallel a (voltageSource e)).Admissible v i → v = e := by
  rintro ⟨_, _, _, hb, _⟩
  exact hb

/-- Tellegen's identity for a two-element series branch: the branch power is the sum of
the element powers, which is the interconnection form of energy conservation. -/
theorem series_power_split {v i va vb : K} (hv : v = va + vb) :
    absorbed v i = absorbed va i + absorbed vb i := by
  simp only [absorbed, hv]
  ring

theorem parallel_power_split {v i ia ib : K} (hi : i = ia + ib) :
    absorbed v i = absorbed v ia + absorbed v ib := by
  simp only [absorbed, hi]
  ring

end Algebraic

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An element is passive when it absorbs nonnegative power at every admissible point.
This is the fixed-operating-point form; it does not by itself bound stored energy. -/
def Passive (a : TwoTerminal K) : Prop := ∀ v i, a.Admissible v i → 0 ≤ absorbed v i

/-- An element is lossless when every admissible operating point absorbs no power. -/
def Lossless (a : TwoTerminal K) : Prop := ∀ v i, a.Admissible v i → absorbed v i = 0

omit [IsStrictOrderedRing K] in
theorem lossless_passive {a : TwoTerminal K} (h : Lossless a) : Passive a :=
  fun v i hvi => le_of_eq (h v i hvi).symm

/-- Passivity of a resistor is exactly nonnegativity of its resistance. The reverse
implication is what forbids modelling an active device as an ideal resistor. -/
theorem resistor_passive_iff (r : K) : Passive (resistor r) ↔ 0 ≤ r := by
  constructor
  · intro h
    have := h (r * 1) 1 rfl
    simpa [absorbed] using this
  · intro hr v i hvi
    rw [show v = r * i from hvi]
    have square : (0 : K) ≤ i * i := mul_self_nonneg i
    have := mul_nonneg hr square
    simp only [absorbed]
    nlinarith

theorem conductor_passive_iff (g : K) : Passive (conductor g) ↔ 0 ≤ g := by
  constructor
  · intro h
    have := h 1 (g * 1) rfl
    simpa [absorbed] using this
  · intro hg v i hvi
    rw [show i = g * v from hvi]
    have square : (0 : K) ≤ v * v := mul_self_nonneg v
    have := mul_nonneg hg square
    simp only [absorbed]
    nlinarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem open_lossless : Lossless (openCircuit (K := K)) := by
  intro v i hvi
  simp [absorbed, show i = 0 from hvi]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem short_lossless : Lossless (shortCircuit (K := K)) := by
  intro v i hvi
  simp [absorbed, show v = 0 from hvi]

/-- An ideal source with nonzero strength is never passive: it delivers power at some
admissible operating point. Sources therefore need an explicit energy budget. -/
theorem voltage_source_not_passive {e : K} (nonzero : e ≠ 0) : ¬Passive (voltageSource e) := by
  intro h
  rcases lt_trichotomy e 0 with he | he | he
  · have := h e 1 rfl
    simp only [absorbed, mul_one] at this
    linarith
  · exact nonzero he
  · have := h e (-1) rfl
    simp only [absorbed, mul_neg, mul_one] at this
    linarith

theorem current_source_not_passive {s : K} (nonzero : s ≠ 0) : ¬Passive (currentSource s) := by
  intro h
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have := h 1 s rfl
    simp only [absorbed, one_mul] at this
    linarith
  · exact nonzero hs
  · have := h (-1) s rfl
    simp only [absorbed, neg_mul, one_mul] at this
    linarith

/-- Passivity is preserved by both interconnections: ideal wiring creates no energy. -/
theorem series_passive {a b : TwoTerminal K} (ha : Passive a) (hb : Passive b) :
    Passive (series a b) := by
  rintro v i ⟨va, vb, hva, hvb, hv⟩
  have pa := ha va i hva
  have pb := hb vb i hvb
  simp only [absorbed] at *
  rw [hv, add_mul]
  linarith

theorem parallel_passive {a b : TwoTerminal K} (ha : Passive a) (hb : Passive b) :
    Passive (parallel a b) := by
  rintro v i ⟨ia, ib, hia, hib, hi⟩
  have pa := ha v ia hia
  have pb := hb v ib hib
  simp only [absorbed] at *
  rw [hi, mul_add]
  linarith

omit [IsStrictOrderedRing K] in
/-- Equivalent elements have the same passivity, so terminal reasoning is invariant
under the Thévenin/Norton and resistor/conductor changes of parameterization. -/
theorem passive_of_equivalent {a b : TwoTerminal K} (h : Equivalent a b) (hb : Passive b) :
    Passive a := fun v i hvi => hb v i ((h v i).mp hvi)

end Ordered
end TwoTerminal
end Synthesis.Domains.Electronics.Element
