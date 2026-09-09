import Synthesis.Semantics.Model

namespace Synthesis.Semantics
set_option autoImplicit false
universe u

/-- Across and through variables may use different scalar/quantity types. Signed flow
is positive into the junction; the domain owns units and physical applicability. -/
structure Terminal (Across Through : Type u) where
  across : Across
  through : Through

def Conservative {Across Through : Type u} [Zero Through] [Add Through]
    (terminals : List (Terminal Across Through)) : Prop :=
  (∀ a ∈ terminals, ∀ b ∈ terminals, a.across = b.across) ∧
  (terminals.map (·.through)).foldr (· + ·) 0 = 0

theorem Conservative.balanced {Across Through : Type u} [Zero Through] [Add Through]
    {terminals : List (Terminal Across Through)} (law : Conservative terminals) :
    (terminals.map (·.through)).foldr (· + ·) 0 = 0 := law.2

end Synthesis.Semantics
