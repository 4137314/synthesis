import Synthesis.Semantics.Model

namespace Synthesis.Design
set_option autoImplicit false
universe u v

/-- A typed value codec must round-trip exactly. Real values need symbolic or external
representations; this interface cannot justify silently rounding them to rationals. -/
structure Encoding (Value : Type u) where
  type : IR.TypeExpr
  encode : Value → IR.Data
  decode : IR.Data → Option Value
  exact : ∀ x, decode (encode x) = some x

/-- Typed terms are indexed by their scope, extension interpretation and result type. -/
structure Expression (extension : IR.Extension) (context : IR.Context) (type : IR.TypeExpr) where
  term : IR.Term
  typed : extension.infer context term = some type

structure Requirement (Observation : Type u) where
  id : ContractId
  contract : Logic.Contract Observation
  /-- Inspectable requirement structure, including envelope and guarantee expressions. -/
  declaration : IR.Operation
  provenance : IR.Provenance := {}

/-- The rich source is authoritative. Its lowering and denotation have an explicit
relation; an IR field with a familiar name alone cannot stand in for that proof. -/
structure Model (Source : Type u) (Observation : Type v) where
  source : Source
  lower : Source → IR.Module
  behavior : Source → Logic.Behavior Observation
  interpretation : Semantics.Interpretation Observation
  represented : ∀ x, interpretation.Meaning (lower source) x ↔ behavior source x
  supported : interpretation.Supported (lower source)
  requirements : List (Requirement Observation) := []
  requirementsRetained : ∀ r ∈ requirements,
    ∃ d ∈ (lower source).definitions, r.declaration ∈ d.operations

/-- Local interfaces and internal state remain Lean types, including trajectories. -/
structure Definition (Parameters : Type u) (Interface State : Type v) where
  admissible : Parameters → Prop
  relation : Parameters → Interface → State → Prop

end Synthesis.Design
