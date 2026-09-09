import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.TwoPort
set_option autoImplicit false

/-! # Impedance parameters of a linear two-port

A linear two-port described by `v₁ = z₁₁ i₁ + z₁₂ i₂`, `v₂ = z₂₁ i₁ + z₂₂ i₂`, in the
passive convention at both ports. The absorbed power is then a quadratic form in the
port currents, and passivity is exactly the definiteness of that form: `passivity_iff`
proves both directions, so the usual parameter inequality is a characterization rather
than a modelling convenience.

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

/-- Determinant of the impedance matrix. It is nonzero exactly when the two-port also
admits an admittance description; see
`Synthesis.Domains.Electronics.TwoPort.Conversion`. -/
def determinant (p : Impedance K) : K := p.z11 * p.z22 - p.z12 * p.z21

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
end Synthesis.Domains.Electronics.TwoPort
