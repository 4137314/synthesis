import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.TwoPort
set_option autoImplicit false

/-! # Two-port networks

A linear two-port is described by its impedance parameters `v₁ = z₁₁ i₁ + z₁₂ i₂`,
`v₂ = z₂₁ i₁ + z₂₂ i₂`, in the passive convention at both ports. The absorbed power is
then a quadratic form in the port currents, and passivity is exactly the definiteness
of that form: `passivity_iff` proves both directions, so the usual parameter inequality
is a characterization rather than a modelling convenience.

The transmission (`ABCD`) description is included because it is the one that composes
under cascading, and the determinant identity `AD - BC = 1` for reciprocal ports is
preserved by cascade composition.

Two-ports here are memoryless and describe one operating point; the parameters may be
real or complex depending on the field chosen, but no frequency dependence is modelled
inside a single value. -/

variable {K : Type*}

/-- Impedance parameters of a linear two-port. -/
structure Impedance (K : Type*) where
  z11 : K
  z12 : K
  z21 : K
  z22 : K

/-- Transmission parameters relating the input pair to the output pair. -/
structure Transmission (K : Type*) where
  a : K
  b : K
  c : K
  d : K

namespace Impedance

section Ring
variable [Field K]

def primaryVoltage (p : Impedance K) (i₁ i₂ : K) : K := p.z11 * i₁ + p.z12 * i₂

def secondaryVoltage (p : Impedance K) (i₁ i₂ : K) : K := p.z21 * i₁ + p.z22 * i₂

/-- Total power absorbed at the two ports. -/
def absorbed (p : Impedance K) (i₁ i₂ : K) : K :=
  p.primaryVoltage i₁ i₂ * i₁ + p.secondaryVoltage i₁ i₂ * i₂

/-- Reciprocity of the two-port: the transfer parameters agree. -/
def Reciprocal (p : Impedance K) : Prop := p.z12 = p.z21

/-- Symmetry: the two ports are interchangeable. -/
def Symmetric (p : Impedance K) : Prop := p.z11 = p.z22 ∧ p.Reciprocal

theorem absorbed_quadratic (p : Impedance K) (i₁ i₂ : K) :
    p.absorbed i₁ i₂ = p.z11 * i₁ ^ 2 + (p.z12 + p.z21) * i₁ * i₂ + p.z22 * i₂ ^ 2 := by
  simp only [absorbed, primaryVoltage, secondaryVoltage]
  ring

/-- `z₁₁` is the open-circuit input impedance, which is how it is measured. -/
theorem open_circuit_primary (p : Impedance K) (i₁ : K) :
    p.primaryVoltage i₁ 0 = p.z11 * i₁ := by
  simp [primaryVoltage]

theorem open_circuit_transfer (p : Impedance K) (i₁ : K) :
    p.secondaryVoltage i₁ 0 = p.z21 * i₁ := by
  simp [secondaryVoltage]

/-- Series-series interconnection adds impedance parameters. -/
def series (p q : Impedance K) : Impedance K :=
  ⟨p.z11 + q.z11, p.z12 + q.z12, p.z21 + q.z21, p.z22 + q.z22⟩

theorem series_absorbed (p q : Impedance K) (i₁ i₂ : K) :
    (series p q).absorbed i₁ i₂ = p.absorbed i₁ i₂ + q.absorbed i₁ i₂ := by
  simp only [absorbed, primaryVoltage, secondaryVoltage, series]
  ring

theorem series_reciprocal {p q : Impedance K} (hp : p.Reciprocal) (hq : q.Reciprocal) :
    (series p q).Reciprocal := by
  simp only [Reciprocal, series] at *
  rw [hp, hq]

/-- A T network of three branch impedances. -/
def tee (left shared right : K) : Impedance K := ⟨left + shared, shared, shared, right + shared⟩

theorem tee_reciprocal (left shared right : K) : (tee left shared right).Reciprocal := rfl

/-- **Realization**: every reciprocal two-port is the T network built from its own
parameters, so reciprocity is exactly the condition for this three-element realization. -/
theorem tee_realizes {p : Impedance K} (reciprocal : p.Reciprocal) :
    tee (p.z11 - p.z12) p.z12 (p.z22 - p.z12) = p := by
  simp only [Reciprocal] at reciprocal
  cases p with
  | mk z11 z12 z21 z22 =>
    simp only [tee, Impedance.mk.injEq] at *
    exact ⟨by ring, trivial, reciprocal, by ring⟩

/-- **Input impedance under load.** Terminating port two with an impedance `Z_L` makes
the driving-point impedance of port one `z₁₁ - z₁₂ z₂₁ / (z₂₂ + Z_L)`. -/
theorem input_impedance_loaded (p : Impedance K) {load i₁ i₂ : K} (driven : i₁ ≠ 0)
    (terminated : p.z22 + load ≠ 0)
    (loaded : p.secondaryVoltage i₁ i₂ = -(load * i₂)) :
    p.primaryVoltage i₁ i₂ / i₁ = p.z11 - p.z12 * p.z21 / (p.z22 + load) := by
  have secondary : i₂ * (p.z22 + load) = -(p.z21 * i₁) := by
    simp only [secondaryVoltage] at loaded
    linear_combination loaded
  rw [div_eq_iff driven]
  simp only [primaryVoltage]
  field_simp
  linear_combination p.z12 * secondary

end Ring

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Definiteness of the port quadratic form is sufficient for passivity. -/
theorem passive_of_definite {p : Impedance K} (input : 0 < p.z11)
    (definite : (p.z12 + p.z21) ^ 2 ≤ 4 * p.z11 * p.z22) (i₁ i₂ : K) : 0 ≤ p.absorbed i₁ i₂ := by
  have square : 0 ≤ (2 * p.z11 * i₁ + (p.z12 + p.z21) * i₂) ^ 2 := sq_nonneg _
  have residual : 0 ≤ (4 * p.z11 * p.z22 - (p.z12 + p.z21) ^ 2) * i₂ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg i₂)
  have scaled : 0 ≤ 4 * p.z11 * p.absorbed i₁ i₂ := by
    have expand : 4 * p.z11 * p.absorbed i₁ i₂ =
        (2 * p.z11 * i₁ + (p.z12 + p.z21) * i₂) ^ 2 +
          (4 * p.z11 * p.z22 - (p.z12 + p.z21) ^ 2) * i₂ ^ 2 := by
      rw [absorbed_quadratic]
      ring
    rw [expand]
    linarith
  nlinarith

/-- Passivity forces the same definiteness condition, so the two are equivalent. -/
theorem definite_of_passive {p : Impedance K} (input : 0 < p.z11)
    (passive : ∀ i₁ i₂ : K, 0 ≤ p.absorbed i₁ i₂) :
    (p.z12 + p.z21) ^ 2 ≤ 4 * p.z11 * p.z22 := by
  have witness := passive (-(p.z12 + p.z21)) (2 * p.z11)
  have expand : p.absorbed (-(p.z12 + p.z21)) (2 * p.z11) =
      p.z11 * (4 * p.z11 * p.z22 - (p.z12 + p.z21) ^ 2) := by
    rw [absorbed_quadratic]
    ring
  rw [expand] at witness
  nlinarith

theorem passivity_iff {p : Impedance K} (input : 0 < p.z11) :
    (∀ i₁ i₂ : K, 0 ≤ p.absorbed i₁ i₂) ↔ (p.z12 + p.z21) ^ 2 ≤ 4 * p.z11 * p.z22 :=
  ⟨definite_of_passive input, fun definite => passive_of_definite input definite⟩

omit [IsStrictOrderedRing K] in
/-- A passive two-port cannot have a negative open-circuit input impedance. -/
theorem input_nonneg_of_passive {p : Impedance K} (passive : ∀ i₁ i₂ : K, 0 ≤ p.absorbed i₁ i₂) :
    0 ≤ p.z11 := by
  have witness := passive 1 0
  rw [absorbed_quadratic] at witness
  simpa using witness

end Ordered
end Impedance

namespace Transmission
variable [Field K]

/-- Determinant of the transmission matrix. -/
def determinant (t : Transmission K) : K := t.a * t.d - t.b * t.c

/-- Cascade composition: the output pair of the first port drives the second. -/
def cascade (first second : Transmission K) : Transmission K :=
  ⟨first.a * second.a + first.b * second.c, first.a * second.b + first.b * second.d,
   first.c * second.a + first.d * second.c, first.c * second.b + first.d * second.d⟩

/-- Reciprocity of a transmission description. -/
def Reciprocal (t : Transmission K) : Prop := t.determinant = 1

/-- The determinant is multiplicative under cascading. -/
theorem determinant_cascade (first second : Transmission K) :
    (cascade first second).determinant = first.determinant * second.determinant := by
  simp only [determinant, cascade]
  ring

/-- **Reciprocity is preserved by cascading**: a chain of reciprocal two-ports is
reciprocal, which is what makes the transmission description composable. -/
theorem cascade_reciprocal {first second : Transmission K}
    (hf : first.Reciprocal) (hs : second.Reciprocal) : (cascade first second).Reciprocal := by
  simp only [Reciprocal] at *
  rw [determinant_cascade, hf, hs, mul_one]

/-- The identity two-port is a lossless pass-through and is reciprocal. -/
def identity : Transmission K := ⟨1, 0, 0, 1⟩

theorem identity_reciprocal : (identity (K := K)).Reciprocal := by
  simp [Reciprocal, determinant, identity]

theorem cascade_identity (t : Transmission K) : cascade t identity = t := by
  simp only [cascade, identity]
  simp

theorem identity_cascade (t : Transmission K) : cascade identity t = t := by
  simp only [cascade, identity]
  simp

theorem cascade_assoc (first second third : Transmission K) :
    cascade (cascade first second) third = cascade first (cascade second third) := by
  simp only [cascade, Transmission.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- A series impedance as a transmission two-port. -/
def seriesImpedance (z : K) : Transmission K := ⟨1, z, 0, 1⟩

/-- A shunt admittance as a transmission two-port. -/
def shuntAdmittance (y : K) : Transmission K := ⟨1, 0, y, 1⟩

theorem seriesImpedance_reciprocal (z : K) : (seriesImpedance z).Reciprocal := by
  simp [Reciprocal, determinant, seriesImpedance]

theorem shuntAdmittance_reciprocal (y : K) : (shuntAdmittance y).Reciprocal := by
  simp [Reciprocal, determinant, shuntAdmittance]

/-- Two series impedances in cascade add, as they must. -/
theorem seriesImpedance_cascade (z w : K) :
    cascade (seriesImpedance z) (seriesImpedance w) = seriesImpedance (z + w) := by
  simp only [cascade, seriesImpedance, Transmission.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- An L section is a series impedance followed by a shunt admittance, and it inherits
reciprocity from its parts. -/
theorem l_section_reciprocal (z y : K) :
    (cascade (seriesImpedance z) (shuntAdmittance y)).Reciprocal :=
  cascade_reciprocal (seriesImpedance_reciprocal z) (shuntAdmittance_reciprocal y)

end Transmission
end Synthesis.Domains.Electronics.TwoPort
