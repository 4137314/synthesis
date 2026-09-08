import Std
import Synthesis.Physics.Quantity

namespace Synthesis.Physics
set_option autoImplicit false

/-- Exact rational coefficients; this does not model rounding or arbitrary real values. -/
abbrev Scalar := Rat

/-- Nonnegative physical parameter with its operating-envelope evidence. -/
structure Nonnegative (dimension : Dimension) where
  quantity : Quantity Rat dimension
  nonnegative : 0 ≤ quantity.value

/-- Strictly positive physical parameter, excluding degenerate constitutive laws. -/
structure Positive (dimension : Dimension) where
  quantity : Quantity Rat dimension
  positive : 0 < quantity.value

/-- Squares are nonnegative even when signed observations are negative. -/
theorem square_nonnegative (x : Rat) : 0 ≤ x * x := by
  rcases Rat.nonneg_total x with h | h
  · exact Rat.mul_nonneg h h
  · have hh := Rat.mul_nonneg h h
    grind

theorem positive_nonnegative {d : Dimension} (x : Positive d) : 0 ≤ x.quantity.value := by
  have h := x.positive
  grind

/-- A nonzero observation dissipates strictly, which distinguishes an operating point
from the degenerate zero state. -/
theorem square_positive {x : Rat} (nonzero : x ≠ 0) : 0 < x * x := by
  rcases Rat.nonneg_total x with h | h
  · exact Rat.mul_pos (Rat.lt_of_le_of_ne h (fun e => nonzero e.symm))
      (Rat.lt_of_le_of_ne h (fun e => nonzero e.symm))
  · have hx : 0 < -x := Rat.lt_of_le_of_ne h (by grind)
    have := Rat.mul_pos hx hx
    grind

/-- Reciprocal parameters of strictly positive coefficients remain strictly positive,
so a dual parameterization stays inside the same operating envelope. -/
theorem reciprocal_positive {x : Rat} (positive : 0 < x) : 0 < 1 / x := by
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.inv_pos.mpr positive

/-- The defining identity of a reciprocal coefficient, stated without an inverse operator. -/
theorem reciprocal_product {x : Rat} (positive : 0 < x) : x * (1 / x) = 1 := by
  have nonzero : x ≠ 0 := by grind
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.mul_inv_cancel x nonzero

end Synthesis.Physics
