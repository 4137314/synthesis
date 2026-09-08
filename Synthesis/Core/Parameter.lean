import Init.Data.Rat
import Synthesis.Core.Dimension

namespace Synthesis

/-- A normalized SI rational literal. Physical-kind distinctions belong to port/theory
contracts; this tag records dimensions, not a complete constitutive semantics. -/
structure Parameter where
  name : String
  dimension : Dimension
  value : Rat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

end Synthesis
