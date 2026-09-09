import Synthesis.Design.Model

namespace Synthesis.Design
set_option autoImplicit false
universe u v

/-- A specification states an envelope and guarantee on observations. It does not
assert feasibility or supply an implementation. -/
structure Specification (Observation : Type u) where
  id : ContractId
  contract : Logic.Contract Observation

/-- Technology restricts the admissible implementation space. Parameters may remain
symbolic in Candidate; aspects identify the explicit technology assumptions. -/
structure TechnologyContext (Candidate : Type u) where
  id : ContractId
  admissible : Candidate → Prop
  aspects : List ContractId := []

/-- Realization is a relation between a candidate and its allowed observations, not
an algorithm or a promise that a solution exists. -/
structure RealizationProblem (Candidate : Type u) (Observation : Type v) where
  specification : Specification Observation
  technology : TechnologyContext Candidate
  behavior : Candidate → Logic.Behavior Observation

structure Realization {Candidate : Type u} {Observation : Type v}
    (problem : RealizationProblem Candidate Observation) where
  candidate : Candidate

/-- Certification includes technology admissibility, feasible behavior in the
specification envelope and satisfaction for every admitted behavior. -/
structure CertifiedRealization {Candidate : Type u} {Observation : Type v}
    (problem : RealizationProblem Candidate Observation) extends Realization problem where
  admissible : problem.technology.admissible candidate
  feasible : ∃ x, problem.behavior candidate x ∧ problem.specification.contract.assumption x
  satisfies : Logic.Contract.Satisfies (problem.behavior candidate) problem.specification.contract

/-- Parameter role identities are extension-defined; admissibility can express sets,
uncertainty, manufacturing variation or calibration without choosing a solver. -/
structure ParameterSpace (Value : Type u) where
  role : ContractId
  admissible : Value → Prop

end Synthesis.Design
