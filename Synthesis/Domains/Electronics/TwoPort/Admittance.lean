import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.TwoPort
set_option autoImplicit false

/-! # Admittance parameters of a linear two-port

The dual description of `Synthesis.Domains.Electronics.TwoPort.Impedance`: the port
currents are driven by the port voltages, `i₁ = y₁₁ v₁ + y₁₂ v₂`, `i₂ = y₂₁ v₁ + y₂₂ v₂`,
still in the passive convention at both ports.

The description is kept separate rather than derived because its natural algebra is
different: admittance parameters add under *parallel-parallel* interconnection, where
impedance parameters do not, and the three-element realization of a reciprocal port is
the Π network rather than the T network. Passivity is again exactly the definiteness of
the port quadratic form, and `passivity_iff` proves both directions.

Conversion between the two descriptions, and the nondegeneracy it requires, is in
`Synthesis.Domains.Electronics.TwoPort.Conversion`. -/

variable {K : Type*}

/-- Admittance parameters of a linear two-port. -/
structure Admittance (K : Type*) where
  y11 : K
  y12 : K
  y21 : K
  y22 : K

namespace Admittance

section Ring
variable [Field K]

def primaryCurrent (p : Admittance K) (v₁ v₂ : K) : K := p.y11 * v₁ + p.y12 * v₂

def secondaryCurrent (p : Admittance K) (v₁ v₂ : K) : K := p.y21 * v₁ + p.y22 * v₂

/-- Total power absorbed at the two ports. -/
def absorbed (p : Admittance K) (v₁ v₂ : K) : K :=
  v₁ * p.primaryCurrent v₁ v₂ + v₂ * p.secondaryCurrent v₁ v₂

/-- Reciprocity of the two-port in the admittance description. -/
def Reciprocal (p : Admittance K) : Prop := p.y12 = p.y21

/-- Determinant of the admittance matrix. -/
def determinant (p : Admittance K) : K := p.y11 * p.y22 - p.y12 * p.y21

/-- Symmetry: the two ports are interchangeable. -/
def Symmetric (p : Admittance K) : Prop := p.y11 = p.y22 ∧ p.Reciprocal

theorem absorbed_quadratic (p : Admittance K) (v₁ v₂ : K) :
    p.absorbed v₁ v₂ = p.y11 * v₁ ^ 2 + (p.y12 + p.y21) * v₁ * v₂ + p.y22 * v₂ ^ 2 := by
  simp only [absorbed, primaryCurrent, secondaryCurrent]
  ring

/-- `y₁₁` is the short-circuit input admittance, which is how it is measured: the
secondary port is shorted, not opened. -/
theorem short_circuit_primary (p : Admittance K) (v₁ : K) :
    p.primaryCurrent v₁ 0 = p.y11 * v₁ := by
  simp [primaryCurrent]

theorem short_circuit_transfer (p : Admittance K) (v₁ : K) :
    p.secondaryCurrent v₁ 0 = p.y21 * v₁ := by
  simp [secondaryCurrent]

/-- **Parallel-parallel interconnection adds admittance parameters.** This is the
composition law that has no counterpart in the impedance description. -/
def parallel (p q : Admittance K) : Admittance K :=
  ⟨p.y11 + q.y11, p.y12 + q.y12, p.y21 + q.y21, p.y22 + q.y22⟩

theorem parallel_current (p q : Admittance K) (v₁ v₂ : K) :
    (parallel p q).primaryCurrent v₁ v₂ =
      p.primaryCurrent v₁ v₂ + q.primaryCurrent v₁ v₂ := by
  simp only [primaryCurrent, parallel]
  ring

theorem parallel_absorbed (p q : Admittance K) (v₁ v₂ : K) :
    (parallel p q).absorbed v₁ v₂ = p.absorbed v₁ v₂ + q.absorbed v₁ v₂ := by
  simp only [absorbed, primaryCurrent, secondaryCurrent, parallel]
  ring

theorem parallel_reciprocal {p q : Admittance K} (hp : p.Reciprocal) (hq : q.Reciprocal) :
    (parallel p q).Reciprocal := by
  simp only [Reciprocal, parallel] at *
  rw [hp, hq]

theorem parallel_comm (p q : Admittance K) : parallel p q = parallel q p := by
  simp only [parallel, Admittance.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem parallel_assoc (p q r : Admittance K) :
    parallel (parallel p q) r = parallel p (parallel q r) := by
  simp only [parallel, Admittance.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- A Π network of three branch admittances: two shunt branches and one bridging branch. -/
def pi (left shared right : K) : Admittance K :=
  ⟨left + shared, -shared, -shared, right + shared⟩

theorem pi_reciprocal (left shared right : K) : (pi left shared right).Reciprocal := rfl

/-- **Realization**: every reciprocal two-port is the Π network built from its own
parameters, the dual of the T realization of the impedance description. -/
theorem pi_realizes {p : Admittance K} (reciprocal : p.Reciprocal) :
    pi (p.y11 + p.y12) (-p.y12) (p.y22 + p.y12) = p := by
  simp only [Reciprocal] at reciprocal
  cases p with
  | mk y11 y12 y21 y22 =>
    simp only [pi, Admittance.mk.injEq] at *
    exact ⟨by ring, by ring, by rw [← reciprocal]; ring, by ring⟩

/-- **Output admittance under a terminated input.** Driving port one through a source
admittance `Y_s` makes the driving-point admittance of port two
`y₂₂ - y₁₂ y₂₁ / (y₁₁ + Y_s)`. -/
theorem output_admittance_loaded (p : Admittance K) {source v₁ v₂ : K} (driven : v₂ ≠ 0)
    (terminated : p.y11 + source ≠ 0)
    (loaded : p.primaryCurrent v₁ v₂ = -(source * v₁)) :
    p.secondaryCurrent v₁ v₂ / v₂ = p.y22 - p.y12 * p.y21 / (p.y11 + source) := by
  have primary : v₁ * (p.y11 + source) = -(p.y12 * v₂) := by
    simp only [primaryCurrent] at loaded
    linear_combination loaded
  rw [div_eq_iff driven]
  simp only [secondaryCurrent]
  field_simp
  linear_combination p.y21 * primary

end Ring

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Definiteness of the port quadratic form is sufficient for passivity. -/
theorem passive_of_definite {p : Admittance K} (input : 0 < p.y11)
    (definite : (p.y12 + p.y21) ^ 2 ≤ 4 * p.y11 * p.y22) (v₁ v₂ : K) : 0 ≤ p.absorbed v₁ v₂ := by
  have square : 0 ≤ (2 * p.y11 * v₁ + (p.y12 + p.y21) * v₂) ^ 2 := sq_nonneg _
  have residual : 0 ≤ (4 * p.y11 * p.y22 - (p.y12 + p.y21) ^ 2) * v₂ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg v₂)
  have scaled : 0 ≤ 4 * p.y11 * p.absorbed v₁ v₂ := by
    have expand : 4 * p.y11 * p.absorbed v₁ v₂ =
        (2 * p.y11 * v₁ + (p.y12 + p.y21) * v₂) ^ 2 +
          (4 * p.y11 * p.y22 - (p.y12 + p.y21) ^ 2) * v₂ ^ 2 := by
      rw [absorbed_quadratic]
      ring
    rw [expand]
    linarith
  nlinarith

/-- Passivity forces the same definiteness condition, so the two are equivalent. -/
theorem definite_of_passive {p : Admittance K} (input : 0 < p.y11)
    (passive : ∀ v₁ v₂ : K, 0 ≤ p.absorbed v₁ v₂) :
    (p.y12 + p.y21) ^ 2 ≤ 4 * p.y11 * p.y22 := by
  have witness := passive (-(p.y12 + p.y21)) (2 * p.y11)
  have expand : p.absorbed (-(p.y12 + p.y21)) (2 * p.y11) =
      p.y11 * (4 * p.y11 * p.y22 - (p.y12 + p.y21) ^ 2) := by
    rw [absorbed_quadratic]
    ring
  rw [expand] at witness
  nlinarith

theorem passivity_iff {p : Admittance K} (input : 0 < p.y11) :
    (∀ v₁ v₂ : K, 0 ≤ p.absorbed v₁ v₂) ↔ (p.y12 + p.y21) ^ 2 ≤ 4 * p.y11 * p.y22 :=
  ⟨definite_of_passive input, fun definite => passive_of_definite input definite⟩

omit [IsStrictOrderedRing K] in
/-- A passive two-port cannot have a negative short-circuit input admittance. -/
theorem input_nonneg_of_passive {p : Admittance K}
    (passive : ∀ v₁ v₂ : K, 0 ≤ p.absorbed v₁ v₂) : 0 ≤ p.y11 := by
  have witness := passive 1 0
  rw [absorbed_quadratic] at witness
  simpa using witness

/-- Passivity is preserved by parallel interconnection: wiring two passive two-ports side
by side creates no energy. -/
theorem parallel_passive {p q : Admittance K}
    (hp : ∀ v₁ v₂ : K, 0 ≤ p.absorbed v₁ v₂) (hq : ∀ v₁ v₂ : K, 0 ≤ q.absorbed v₁ v₂)
    (v₁ v₂ : K) : 0 ≤ (parallel p q).absorbed v₁ v₂ := by
  rw [parallel_absorbed]
  linarith [hp v₁ v₂, hq v₁ v₂]

end Ordered
end Admittance
end Synthesis.Domains.Electronics.TwoPort
