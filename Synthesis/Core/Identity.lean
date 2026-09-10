import Init.Data.Rat
import Synthesis.Core.Dimension

namespace Synthesis
set_option autoImplicit false
universe u

/-- Local identity. Display labels are separate annotations. -/
structure Symbol where
  text : String
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq
instance : Coe String Symbol := ⟨Symbol.mk⟩

/-- A qualified identity is a sequence, not a concatenated path. -/
structure QualifiedId where
  segments : List String
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

instance : Hashable QualifiedId := ⟨fun id => hash id.segments⟩

/-- Version belongs to the semantic contract, independently of the interchange schema. -/
structure ContractId where
  name : QualifiedId
  version : Nat := 1
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def ContractId.named (owner name : String) (version : Nat := 1) : ContractId :=
  ⟨⟨[owner, name]⟩, version⟩

def ContractId.valid (id : ContractId) : Bool :=
  !id.name.segments.isEmpty && id.name.segments.all (!·.isEmpty) && id.version > 0

/-- Kind identity is stronger than dimensional equality. -/
structure QuantityKind where
  id : ContractId
  dimension : Dimension
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- A value tagged with a physical kind and an independently chosen scalar. -/
structure KindQuantity (Scalar : Type u) (kind : QuantityKind) where
  value : Scalar

/-- Affine source units are represented explicitly; offsets are never multiplied as units. -/
structure AffineUnit (kind : QuantityKind) where
  id : ContractId
  scale : Rat
  offset : Rat
  nonzero : scale ≠ 0

def AffineUnit.normalize {kind : QuantityKind} (unit : AffineUnit kind) (x : Rat) :
    KindQuantity Rat kind := ⟨unit.scale * x + unit.offset⟩

end Synthesis
