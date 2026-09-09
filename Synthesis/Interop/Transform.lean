import Synthesis.Semantics.Model

namespace Synthesis.Interop
set_option autoImplicit false
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}

/-- Requirements are propositions indexed by the actual source, not capability labels. -/
structure Requirement (Source : Type u) where
  id : ContractId
  holds : Source → Prop

/-- Executable sufficiency checking returns evidence. Failure never fabricates data. -/
structure Checker (requirement : Requirement A) where
  check : (source : A) → Except (List IR.Diagnostic) (PLift (requirement.holds source))

/-- Traceability is many-to-many; loss and generated obligations are explicit. -/
structure Trace where
  source : List IR.EntityRef
  target : List IR.EntityRef
  deriving Repr

/-- Compose many-to-many trace links through an explicitly shared intermediate
revision. Unmatched links remain in the stage lineage, not in this end-to-end view. -/
def Trace.compose (first second : List Trace) : List Trace :=
  first.flatMap fun a => second.filterMap fun b =>
    if a.target.any (fun middle => b.source.contains middle) then
      some ⟨a.source, b.target⟩ else none

structure Disclosure where
  consumed : List ContractId := []
  preserved : List ContractId := []
  erased : List ContractId := []
  assumed : List ContractId := []
  derived : List ContractId := []
  diagnostics : List IR.Diagnostic := []
  obligations : List IR.Diagnostic := []
  trace : List Trace := []
  deriving Repr

structure Result (Target : Type u) where
  value : Target
  disclosure : Disclosure

/-- Stages may change representation type. Guarantees are separate proof objects. -/
structure Stage (Source : Type u) (Target : Type v) where
  id : ContractId
  run : Source → Except (List IR.Diagnostic) (Result Target)

def Stage.andThen (first : Stage A B) (second : Stage B C) (id : ContractId) : Stage A C where
  id := id
  run source :=
    match first.run source with
    | .error errors => .error errors
    | .ok a => match second.run a.value with
      | .error errors => .error errors
      | .ok b => .ok ⟨b.value, {
      consumed := a.disclosure.consumed ++ b.disclosure.consumed
      preserved := []
      erased := a.disclosure.erased ++ b.disclosure.erased
      assumed := a.disclosure.assumed ++ b.disclosure.assumed
      derived := a.disclosure.derived ++ b.disclosure.derived
      diagnostics := a.disclosure.diagnostics ++ b.disclosure.diagnostics
      obligations := a.disclosure.obligations ++ b.disclosure.obligations
      trace := a.disclosure.trace ++ b.disclosure.trace }⟩

/-- A successful stage has a proved postcondition; no guarantee is inferred from its name. -/
def Establishes (stage : Stage A B) (relation : A → B → Prop) : Prop :=
  ∀ a result, stage.run a = .ok result → relation a result.value

theorem Stage.andThen_establishes (first : Stage A B) (second : Stage B C) (id : ContractId)
    (P : A → B → Prop) (Q : B → C → Prop)
    (hp : Establishes first P) (hq : Establishes second Q) :
    Establishes (first.andThen second id) (fun a c => ∃ b, P a b ∧ Q b c) := by
  intro a result h
  cases ha : first.run a with
  | error errors => simp [Stage.andThen, ha] at h
  | ok middle =>
    cases hb : second.run middle.value with
    | error errors => simp [Stage.andThen, ha, hb] at h
    | ok output =>
      simp only [Stage.andThen, ha, hb, Except.ok.injEq] at h
      subst result
      exact ⟨middle.value, hp a middle ha, hq middle.value output hb⟩

/-- Proof obligations are rich Lean propositions. A diagnostic is only their public
explanation; it does not discharge the obligation. -/
structure Obligation where
  id : ContractId
  claim : Prop
  diagnostic : IR.Diagnostic

/-- Behavioral refinement allows fewer concrete behaviors under an explicit observation map. -/
def Refines {X : Type u} {Y : Type v} (concrete : Logic.Behavior X)
    (abstract : Logic.Behavior Y) (observe : X → Y) : Prop :=
  ∀ x, concrete x → abstract (observe x)

/-- Equality of projected behavior additionally requires every abstract behavior to lift. -/
def Equivalent {X : Type u} {Y : Type v} (concrete : Logic.Behavior X)
    (abstract : Logic.Behavior Y) (observe : X → Y) : Prop :=
  Refines concrete abstract observe ∧ ∀ y, abstract y → ∃ x, concrete x ∧ observe x = y

theorem Refines.trans {X : Type u} {Y : Type v} {Z : Type w}
    {a : Logic.Behavior X} {b : Logic.Behavior Y} {c : Logic.Behavior Z}
    {f : X → Y} {g : Y → Z} (ab : Refines a b f) (bc : Refines b c g) :
    Refines a c (g ∘ f) := fun x hx => bc (f x) (ab x hx)

/-- Refinement alone can be empty: feasibility must be supplied independently. -/
theorem Refines.satisfies {X : Type u} {Y : Type v}
    {a : Logic.Behavior X} {b : Logic.Behavior Y} {f : X → Y}
    (h : Refines a b f) (requirement : Logic.Contract Y)
    (correct : Logic.Contract.Satisfies b requirement) :
    Logic.Contract.Satisfies a ⟨requirement.assumption ∘ f, requirement.guarantee ∘ f⟩ :=
  fun x hx ha => correct (f x) (h x hx) ha

/-- Non-vacuous refinement in an envelope, with separate concrete feasibility. -/
structure RefinementCertificate {X : Type u} {Y : Type v}
    (concrete : Logic.Behavior X) (abstract : Logic.Behavior Y)
    (observe : X → Y) (envelope : Logic.Behavior Y) : Prop where
  refines : Refines concrete abstract observe
  feasible : ∃ x, concrete x ∧ envelope (observe x)

/-- External artifact producers have an evidence-gated entry point and a target version.
Artifacts remain outside the Lean trust boundary unless separately related by proofs. -/
structure Exporter (Source : Type u) (Artifact : Type v) where
  target : ContractId
  requirement : Requirement Source
  checker : Checker requirement
  emit : (source : Source) → requirement.holds source →
    Except (List IR.Diagnostic) (Result Artifact)

def Exporter.run (exporter : Exporter A B) (source : A) :
    Except (List IR.Diagnostic) (Result B) :=
  match exporter.checker.check source with
  | .error errors => .error errors
  | .ok proof => exporter.emit source proof.down

/-- An unsatisfied prerequisite cannot reach artifact production through run. -/
theorem Exporter.rejects_unsatisfied (exporter : Exporter A B) (source : A)
    (missing : ¬exporter.requirement.holds source) :
    ∃ errors, exporter.run source = .error errors := by
  cases h : exporter.checker.check source with
  | error errors => exact ⟨errors, by simp [Exporter.run, h]⟩
  | ok proof => exact False.elim (missing proof.down)

end Synthesis.Interop
