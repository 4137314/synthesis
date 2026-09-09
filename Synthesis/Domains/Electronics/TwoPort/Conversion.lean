import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Synthesis.Domains.Electronics.TwoPort.Admittance
import Synthesis.Domains.Electronics.TwoPort.Impedance
import Synthesis.Domains.Electronics.TwoPort.Transmission

namespace Synthesis.Domains.Electronics.TwoPort
set_option autoImplicit false

/-! # Conversion between two-port descriptions

The impedance, admittance and transmission parameters describe the same two-port in
different coordinates, but the changes of coordinates are *partial*: a two-port has an
admittance description only when its impedance determinant is nonzero, and a transmission
description only when its transfer parameter is nonzero. An ideal transformer, for
instance, has no impedance description at all.

Every conversion below therefore carries its nondegeneracy hypothesis explicitly, and
each is proved correct in the only sense that matters at the terminals: the converted
parameters reproduce the same relation between the port variables. Round trips and the
preservation of reciprocity are proved rather than assumed, and
`transmission_determinant` shows that the transmission reciprocity identity `AD - BC = 1`
is exactly impedance reciprocity `z₁₂ = z₂₁`. -/

variable {K : Type*}
variable [Field K]

/-- Admittance parameters of a two-port given by its impedance parameters. The inverse of
the impedance matrix exists only away from a vanishing determinant. -/
def Impedance.toAdmittance (p : Impedance K) : Admittance K :=
  ⟨p.z22 / p.determinant, -p.z12 / p.determinant,
   -p.z21 / p.determinant, p.z11 / p.determinant⟩

/-- Impedance parameters of a two-port given by its admittance parameters. -/
def Admittance.toImpedance (p : Admittance K) : Impedance K :=
  ⟨p.y22 / p.determinant, -p.y12 / p.determinant,
   -p.y21 / p.determinant, p.y11 / p.determinant⟩

/-- **The conversion is correct at the primary port**: the admittance parameters
reproduce the port current that the impedance parameters imply. -/
theorem toAdmittance_primary {p : Impedance K} (nondegenerate : p.determinant ≠ 0) (i₁ i₂ : K) :
    p.toAdmittance.primaryCurrent (p.primaryVoltage i₁ i₂) (p.secondaryVoltage i₁ i₂) = i₁ := by
  simp only [Impedance.toAdmittance, Admittance.primaryCurrent, Impedance.primaryVoltage,
    Impedance.secondaryVoltage]
  field_simp
  simp only [Impedance.determinant]
  ring

/-- The conversion is correct at the secondary port as well. -/
theorem toAdmittance_secondary {p : Impedance K} (nondegenerate : p.determinant ≠ 0) (i₁ i₂ : K) :
    p.toAdmittance.secondaryCurrent (p.primaryVoltage i₁ i₂) (p.secondaryVoltage i₁ i₂) = i₂ := by
  simp only [Impedance.toAdmittance, Admittance.secondaryCurrent, Impedance.primaryVoltage,
    Impedance.secondaryVoltage]
  field_simp
  simp only [Impedance.determinant]
  ring

/-- The determinants are reciprocal, so a nondegenerate two-port converts back. -/
theorem toAdmittance_determinant {p : Impedance K} (nondegenerate : p.determinant ≠ 0) :
    p.toAdmittance.determinant * p.determinant = 1 := by
  simp only [Impedance.toAdmittance, Admittance.determinant]
  field_simp
  simp only [Impedance.determinant]
  ring

/-- The converted determinant is the reciprocal of the original one, which is the form
the round trip needs. -/
theorem toAdmittance_determinant_inv {p : Impedance K} (nondegenerate : p.determinant ≠ 0) :
    p.toAdmittance.determinant = (p.determinant)⁻¹ := by
  simp only [Impedance.toAdmittance, Admittance.determinant]
  field_simp
  simp only [Impedance.determinant]
  ring

/-- **Round trip.** Converting to admittance parameters and back recovers the original
impedance description exactly. -/
theorem toImpedance_toAdmittance {p : Impedance K} (nondegenerate : p.determinant ≠ 0) :
    p.toAdmittance.toImpedance = p := by
  have inverse := toAdmittance_determinant_inv nondegenerate
  cases p with
  | mk z11 z12 z21 z22 =>
    simp only [Admittance.toImpedance, Impedance.mk.injEq, inverse]
    simp only [Impedance.toAdmittance]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp

/-- Reciprocity survives the change of coordinates. -/
theorem toAdmittance_reciprocal {p : Impedance K} (reciprocal : p.Reciprocal) :
    p.toAdmittance.Reciprocal := by
  simp only [Impedance.Reciprocal] at reciprocal
  simp only [Admittance.Reciprocal, Impedance.toAdmittance, reciprocal]

/-! ## Transmission parameters

The transmission description exists when the forward transfer impedance is nonzero: a
two-port that transmits nothing has no `ABCD` matrix. -/

/-- Transmission parameters of a two-port given by its impedance parameters. -/
def Impedance.toTransmission (p : Impedance K) : Transmission K :=
  ⟨p.z11 / p.z21, p.determinant / p.z21, 1 / p.z21, p.z22 / p.z21⟩

/-- **The transmission determinant is the ratio of the transfer impedances.** Everything
about reciprocity in the transmission description follows from this single identity. -/
theorem transmission_determinant {p : Impedance K} (transmitting : p.z21 ≠ 0) :
    p.toTransmission.determinant = p.z12 / p.z21 := by
  simp only [Impedance.toTransmission, Transmission.determinant]
  field_simp
  simp only [Impedance.determinant]
  ring

/-- **The two notions of reciprocity agree**: the transmission identity `AD - BC = 1` holds
exactly when the impedance transfer parameters are equal. -/
theorem toTransmission_reciprocal_iff {p : Impedance K} (transmitting : p.z21 ≠ 0) :
    p.toTransmission.Reciprocal ↔ p.Reciprocal := by
  rw [Transmission.Reciprocal, transmission_determinant transmitting, Impedance.Reciprocal,
    div_eq_one_iff_eq transmitting]

/-- A reciprocal two-port has a unit transmission determinant, the form used when
cascading. -/
theorem toTransmission_reciprocal {p : Impedance K} (transmitting : p.z21 ≠ 0)
    (reciprocal : p.Reciprocal) : p.toTransmission.Reciprocal :=
  (toTransmission_reciprocal_iff transmitting).mpr reciprocal

/-- **The T network agrees with its ladder of transmission elements.** Converting the T
impedance description into transmission parameters gives exactly the cascade of a series
impedance, a shunt admittance and a second series impedance. This checks the two
catalogs against each other rather than trusting that they agree. -/
theorem tee_transmission_cascade {shared : K} (transmitting : shared ≠ 0) (left right : K) :
    (Impedance.tee left shared right).toTransmission =
      Transmission.cascade (Transmission.seriesImpedance left)
        (Transmission.cascade (Transmission.shuntAdmittance (1 / shared))
          (Transmission.seriesImpedance right)) := by
  simp only [Impedance.toTransmission, Impedance.tee, Impedance.determinant,
    Transmission.cascade, Transmission.seriesImpedance, Transmission.shuntAdmittance,
    Transmission.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | (field_simp; try ring)

end Synthesis.Domains.Electronics.TwoPort
