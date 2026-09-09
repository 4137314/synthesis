import Synthesis.Domains.Electronics.Element.Basic

namespace Synthesis.Domains.Electronics.Element
set_option autoImplicit false

/-! # Series and parallel interconnection of two-terminal elements

Interconnection is defined by the Kirchhoff constraint it imposes, not by an algebraic
formula on parameters: a series pair shares the branch current and adds voltages, a
parallel pair shares the terminal voltage and adds currents. Both are relations on the
admissible sets, so they compose ideal sources as readily as passive elements.

The closed parameter forms of the interconnections (product over sum and the rest) are
proved separately in `Synthesis.Domains.Electronics.Resistive`; here the results are the
structural ones: commutativity, associativity, neutral elements, and the two power
splitting identities that are the interconnection form of energy conservation. -/

variable {K : Type*}

namespace TwoTerminal
section Algebraic
variable [Field K]

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
end TwoTerminal
end Synthesis.Domains.Electronics.Element
