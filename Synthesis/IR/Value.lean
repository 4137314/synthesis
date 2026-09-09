import Synthesis.Core.Identity

namespace Synthesis.IR
set_option autoImplicit false

/-- Recursive data, never a Lean closure. Extension contracts determine its meaning. -/
inductive Data where
  | rational (value : Rat)
  | integer (value : Int)
  | text (value : String)
  | symbol (value : Symbol)
  | sequence (values : List Data)
  | tagged (contract : ContractId) (values : List Data)
  deriving Repr

mutual
  def Data.decEq (a b : Data) : Decidable (a = b) :=
    match a, b with
    | .rational a0, .rational b0 =>
      decidable_of_iff (a0 = b0) (by simp)
    | .integer a0, .integer b0 =>
      decidable_of_iff (a0 = b0) (by simp)
    | .text a0, .text b0 =>
      decidable_of_iff (a0 = b0) (by simp)
    | .symbol a0, .symbol b0 =>
      decidable_of_iff (a0 = b0) (by simp)
    | .sequence a0, .sequence b0 =>
      haveI := Data.listDecEq a0 b0
      decidable_of_iff (a0 = b0) (by simp)
    | .tagged a0 a1, .tagged b0 b1 =>
      haveI := Data.listDecEq a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .rational _, .integer _ => isFalse (by intro h; cases h)
    | .rational _, .text _ => isFalse (by intro h; cases h)
    | .rational _, .symbol _ => isFalse (by intro h; cases h)
    | .rational _, .sequence _ => isFalse (by intro h; cases h)
    | .rational _, .tagged _ _ => isFalse (by intro h; cases h)
    | .integer _, .rational _ => isFalse (by intro h; cases h)
    | .integer _, .text _ => isFalse (by intro h; cases h)
    | .integer _, .symbol _ => isFalse (by intro h; cases h)
    | .integer _, .sequence _ => isFalse (by intro h; cases h)
    | .integer _, .tagged _ _ => isFalse (by intro h; cases h)
    | .text _, .rational _ => isFalse (by intro h; cases h)
    | .text _, .integer _ => isFalse (by intro h; cases h)
    | .text _, .symbol _ => isFalse (by intro h; cases h)
    | .text _, .sequence _ => isFalse (by intro h; cases h)
    | .text _, .tagged _ _ => isFalse (by intro h; cases h)
    | .symbol _, .rational _ => isFalse (by intro h; cases h)
    | .symbol _, .integer _ => isFalse (by intro h; cases h)
    | .symbol _, .text _ => isFalse (by intro h; cases h)
    | .symbol _, .sequence _ => isFalse (by intro h; cases h)
    | .symbol _, .tagged _ _ => isFalse (by intro h; cases h)
    | .sequence _, .rational _ => isFalse (by intro h; cases h)
    | .sequence _, .integer _ => isFalse (by intro h; cases h)
    | .sequence _, .text _ => isFalse (by intro h; cases h)
    | .sequence _, .symbol _ => isFalse (by intro h; cases h)
    | .sequence _, .tagged _ _ => isFalse (by intro h; cases h)
    | .tagged _ _, .rational _ => isFalse (by intro h; cases h)
    | .tagged _ _, .integer _ => isFalse (by intro h; cases h)
    | .tagged _ _, .text _ => isFalse (by intro h; cases h)
    | .tagged _ _, .symbol _ => isFalse (by intro h; cases h)
    | .tagged _ _, .sequence _ => isFalse (by intro h; cases h)
  termination_by structural a

  def Data.listDecEq (a b : List Data) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      haveI := Data.decEq x y
      haveI := Data.listDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
  termination_by structural a
end

instance : DecidableEq Data := Data.decEq


/-- Open type application: bit widths, array shapes, kinds and scalar models are data. -/
structure TypeExpr where
  constructor : ContractId
  arguments : List Data := []
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- References are scoped to the containing definition or operation body. -/
inductive Term where
  | literal (type : TypeExpr) (value : Data)
  | variable (name : Symbol)
  | apply (operation : ContractId) (arguments : List Term)
  deriving Repr

mutual
  def Term.decEq (a b : Term) : Decidable (a = b) :=
    match a, b with
    | .literal a0 a1, .literal b0 b1 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .variable a0, .variable b0 =>
      decidable_of_iff (a0 = b0) (by simp)
    | .apply a0 a1, .apply b0 b1 =>
      haveI := Term.listDecEq a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .literal _ _, .variable _ => isFalse (by intro h; cases h)
    | .literal _ _, .apply _ _ => isFalse (by intro h; cases h)
    | .variable _, .literal _ _ => isFalse (by intro h; cases h)
    | .variable _, .apply _ _ => isFalse (by intro h; cases h)
    | .apply _ _, .literal _ _ => isFalse (by intro h; cases h)
    | .apply _ _, .variable _ => isFalse (by intro h; cases h)
  termination_by structural a

  def Term.listDecEq (a b : List Term) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      haveI := Term.decEq x y
      haveI := Term.listDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
  termination_by structural a
end

instance : DecidableEq Term := Term.decEq


structure Binding where
  name : Symbol
  value : Term
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- No initializer means externally supplied. Constraints live in explicit operations. -/
structure Parameter where
  name : Symbol
  type : TypeExpr
  value : Option Term := none
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Attribute where
  contract : ContractId
  value : Data
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure SourceSpan where
  source : String
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- External IDs and derivation lineage remain data and survive interchange. -/
structure Provenance where
  source : Option SourceSpan := none
  origin : Option QualifiedId := none
  parents : List QualifiedId := []
  transformation : Option ContractId := none
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Annotations have no semantic force; semantic data belongs in attributes. -/
structure Annotation where
  key : QualifiedId
  value : Data
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

end Synthesis.IR
