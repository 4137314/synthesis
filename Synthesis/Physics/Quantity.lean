import Synthesis.Core.Dimension

namespace Synthesis.Physics

/-- Dimension-indexed values, independent of the scalar model chosen by a domain.
Units must be normalized by the domain frontend; affine temperatures need their own model. -/
structure Quantity (Scalar : Type u) (dimension : Dimension) where
  value : Scalar
  deriving Repr, DecidableEq

def Quantity.add [Add Scalar] (a b : Quantity Scalar d) : Quantity Scalar d :=
  ⟨a.value + b.value⟩

def Quantity.mul [Mul Scalar] (a : Quantity Scalar d) (b : Quantity Scalar e) :
    Quantity Scalar (d.mul e) := ⟨a.value * b.value⟩

/-- A constitutive equation can compare only quantities of the same dimension. -/
structure Equation (Scalar : Type u) (dimension : Dimension) where
  lhs : Quantity Scalar dimension
  rhs : Quantity Scalar dimension

def Equation.Holds (equation : Equation Scalar d) : Prop :=
  equation.lhs = equation.rhs

/-- Integrated balance over an interval, with signed exchange and generation.
The dimension is that of the stored quantity, not its time derivative. -/
structure Balance (Scalar : Type u) (dimension : Dimension) where
  before : Quantity Scalar dimension
  after : Quantity Scalar dimension
  incoming : Quantity Scalar dimension
  outgoing : Quantity Scalar dimension
  generated : Quantity Scalar dimension

def Balance.Holds [Add Scalar] (balance : Balance Scalar d) : Prop :=
  balance.after.value + balance.outgoing.value =
    (balance.before.value + balance.incoming.value) + balance.generated.value

/-- A concrete exact-integer instance, not an assumption about all physical models. -/
theorem Balance.closed_conserves {balance : Balance Int d}
    (law : balance.Holds) (hin : balance.incoming.value = 0)
    (hout : balance.outgoing.value = 0) (hgen : balance.generated.value = 0) :
    balance.after = balance.before := by
  have h : balance.after.value = balance.before.value := by
    simpa [Holds, hin, hout, hgen] using law
  exact congrArg Quantity.mk h

end Synthesis.Physics
