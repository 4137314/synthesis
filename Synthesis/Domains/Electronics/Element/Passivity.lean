import Synthesis.Domains.Electronics.Element.Interconnect

namespace Synthesis.Domains.Electronics.Element
set_option autoImplicit false

/-! # Passivity and losslessness of a two-terminal element

Passivity is a property of the admissible set, so it is stated once and transported
along terminal equivalence and along both interconnections. The characterizations are
biconditional: `resistor_passive_iff` forbids modelling an active device as an ideal
resistor, and the two source lemmas prove that an ideal source is never passive, which
is why source certificates must carry an operating-envelope assumption.

This is the fixed-operating-point form of passivity. It bounds no stored energy and
says nothing about a trajectory in time; the incremental energy statements belong to
`Synthesis.Domains.Electronics.Storage`. -/

variable {K : Type*}

namespace TwoTerminal

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
