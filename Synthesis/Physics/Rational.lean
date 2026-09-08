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

end Synthesis.Physics
