import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.TwoPort
set_option autoImplicit false

/-! # Transmission parameters of a linear two-port

The `ABCD` description is the one that composes under cascading: `cascade` is matrix
multiplication, the determinant is multiplicative under it, and the reciprocity identity
`AD - BC = 1` is therefore preserved along a chain. That makes the transmission form the
natural algebra for ladder networks, and `cascade_assoc` with the two identity laws shows
the composition is a monoid.

Like the impedance description this is memoryless and describes one operating point. -/

variable {K : Type*}

/-- Transmission parameters relating the input pair to the output pair. -/
structure Transmission (K : Type*) where
  a : K
  b : K
  c : K
  d : K

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
