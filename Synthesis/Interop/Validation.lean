import Synthesis.Interop.Transform
import Synthesis.IR.Render

namespace Synthesis.Interop
set_option autoImplicit false
universe u v w

/-- An untrusted generator's output becomes certified only through evidence of the
specified relation. The generator itself is not in this guarantee's trust boundary. -/
structure CertifiedTranslation {A : Type u} {B : Type v}
    (relation : A → B → Prop) (source : A) where
  target : B
  correct : relation source target

/-- Validators may reject or return kernel-checked evidence. External success reports
must use EvidenceReport, not this proof-producing interface. -/
structure TranslationValidator (A : Type u) (B : Type v) (relation : A → B → Prop) where
  id : ContractId
  check : (source : A) → (target : B) →
    Except (List IR.Diagnostic) (PLift (relation source target))

def TranslationValidator.certify {A : Type u} {B : Type v} {relation : A → B → Prop}
    (validator : TranslationValidator A B relation) (source : A) (target : B) :
    Except (List IR.Diagnostic) (CertifiedTranslation relation source) :=
  match validator.check source target with
  | .error errors => .error errors
  | .ok evidence => .ok ⟨target, evidence.down⟩

/-- Reports are inspectable claims, never proofs. The open method contract can identify
an external tool, experiment, test, assumption or unresolved obligation. -/
inductive EvidenceStatus where
  | passed | failed | inconclusive | notRun | assumed
  deriving Repr, DecidableEq, BEq

structure EvidenceReport where
  id : ContractId
  method : ContractId
  subjects : List IR.LocatedEntity
  status : EvidenceStatus
  claim : ContractId
  tool : Option ContractId := none
  inputs : List RevisionRef := []
  outputs : List RevisionRef := []
  certificate : Option RevisionRef := none
  statement : String
  dependencies : List ContractId := []
  provenance : IR.Provenance := {}
  deriving Repr, DecidableEq

/-- Formal evidence requires an actual proof of the proposition chosen by the caller. -/
structure ProofEvidence (claim : Prop) where
  id : ContractId
  proof : claim

/-- Requirement conjunction is available to any stage, not just exporters. -/
def Requirement.and {A : Type u} (a b : Requirement A) (id : ContractId) : Requirement A :=
  ⟨id, fun source => a.holds source ∧ b.holds source⟩

def Checker.and {A : Type u} {a b : Requirement A} (first : Checker a)
    (second : Checker b) (id : ContractId) : Checker (a.and b id) where
  check source := match first.check source, second.check source with
    | .ok ha, .ok hb => .ok ⟨ha.down, hb.down⟩
    | .error ea, .error eb => .error (ea ++ eb)
    | .error e, _ => .error e
    | _, .error e => .error e

/-- Guard arbitrary heterogeneous stages with proof-producing sufficiency checking. -/
def Stage.requiring {A : Type u} {B : Type v} (stage : Stage A B)
    {requirement : Requirement A} (checker : Checker requirement) : Stage A B where
  id := stage.id
  run source := match checker.check source with
    | .error errors => .error errors
    | .ok _ => stage.run source

/-- Equivalence composes through the actual observation functions and lifting proofs. -/
theorem Equivalent.trans {X : Type u} {Y : Type v} {Z : Type w}
    {a : Logic.Behavior X} {b : Logic.Behavior Y} {c : Logic.Behavior Z}
    {f : X → Y} {g : Y → Z} (ab : Equivalent a b f) (bc : Equivalent b c g) :
    Equivalent a c (g ∘ f) := by
  refine ⟨ab.1.trans bc.1, ?_⟩
  intro z hz
  obtain ⟨y, hy, ey⟩ := bc.2 z hz
  obtain ⟨x, hx, ex⟩ := ab.2 y hy
  exact ⟨x, hx, by simp [ex, ey]⟩

/-- Schema transitions are explicit typed stages. Version labels do not themselves
prove that a particular value conforms to a schema; use source/target validation. -/
structure Migration (Source : Type u) (Target : Type v) where
  sourceSchema : Nat
  targetSchema : Nat
  stage : Stage Source Target

def Migration.andThen {A : Type u} {B : Type v} {C : Type w}
    (first : Migration A B) (second : Migration B C) (id : ContractId) :
    Except (List IR.Diagnostic) (Migration A C) :=
  if first.targetSchema == second.sourceSchema then
    .ok ⟨first.sourceSchema, second.targetSchema, first.stage.andThen second.stage id⟩
  else .error [IR.Diagnostic.error "SYN-IR-MIGRATION-VERSION"
    "Migration stages have incompatible intermediate schema versions."]

/-- A profile is descriptive tooling data. The exporter's checker, not this manifest,
is authoritative about whether a particular source satisfies prerequisites. -/
structure BackendProfile where
  identity : ContractId
  target : ContractId
  sourceForm : ContractId
  supportedContracts : List ContractId := []
  unsupportedContracts : List ContractId := []
  description : String := ""

/-- A profiled exporter binds documentation identity to the actual target contract. -/
structure Backend (Source : Type u) (Artifact : Type v) where
  profile : BackendProfile
  exporter : Exporter Source Artifact
  targetAgrees : profile.target = exporter.target

def Disclosure.render (disclosure : Disclosure) : String :=
  let line := fun label ids => label ++ ": " ++
    String.intercalate ", " (ids.map IR.renderContract)
  String.intercalate "\n" [line "consumed" disclosure.consumed,
    line "preserved (reported)" disclosure.preserved,
    line "erased" disclosure.erased, line "assumed" disclosure.assumed,
    line "derived" disclosure.derived,
    "obligations: " ++ toString disclosure.obligations.length,
    "trace links: " ++ toString disclosure.trace.length] ++
    String.join ((disclosure.diagnostics ++ disclosure.obligations).map
      (fun diagnostic => "\n" ++ diagnostic.render))

/-- Terminal presentation retains revision boundaries; it makes no preservation claim. -/
def Trace.render (trace : Trace) : String :=
  s!"{IR.renderRevision trace.sourceRevision} -> {IR.renderRevision trace.targetRevision}" ++
    "\n  source: " ++ String.intercalate ", " (trace.source.map IR.EntityRef.render) ++
    "\n  target: " ++ String.intercalate ", " (trace.target.map IR.EntityRef.render)

def EvidenceStatus.render : EvidenceStatus → String
  | .passed => "passed" | .failed => "failed" | .inconclusive => "inconclusive"
  | .notRun => "not-run" | .assumed => "assumed"

/-- Reports always print their method alongside status: passed is not a proof tier. -/
def EvidenceReport.render (report : EvidenceReport) : String :=
  s!"{IR.renderContract report.id}: {report.status.render} ({IR.renderContract report.method})" ++
    s!"\n  claim: {IR.renderContract report.claim}\n  {report.statement}" ++
    String.join (report.subjects.map (fun subject => "\n  subject: " ++ subject.render)) ++
    (report.tool.map (fun tool => "\n  tool: " ++ IR.renderContract tool) |>.getD "")

/-- Contravariant requirements let pipelines reuse a prerequisite on a projected
source view without changing its meaning. -/
def Requirement.contramap {A : Type u} {B : Type v} (requirement : Requirement A)
    (view : B → A) (id : ContractId) : Requirement B :=
  ⟨id, fun source => requirement.holds (view source)⟩

def Checker.contramap {A : Type u} {B : Type v} {requirement : Requirement A}
    (checker : Checker requirement) (view : B → A) (id : ContractId) :
    Checker (requirement.contramap view id) := ⟨fun source => checker.check (view source)⟩

/-- Encoding correctness is independent from semantic lowering. This optional
interface requires an exact syntactic round-trip proof, not an assurance label. -/
structure RoundTripEncoder (Value Wire : Type) where
  codec : IR.Codec Value Wire
  exact : codec.Exact

theorem RoundTripEncoder.injective {Value Wire : Type} (encoder : RoundTripEncoder Value Wire)
    {a b : Value} (h : encoder.codec.encode a = encoder.codec.encode b) : a = b := by
  have decoded := congrArg encoder.codec.decode h
  rw [encoder.exact a, encoder.exact b] at decoded
  exact Except.ok.inj decoded

/-- A validated translation's provenance is separate from the proof. Revision
functions are explicit package contracts, never inferred from local entity paths. -/
structure TracedTranslation {A : Type u} {B : Type v} (relation : A → B → Prop)
    (source : A) (sourceRevision : RevisionRef) (targetRevision : B → RevisionRef)
    extends CertifiedTranslation relation source where
  trace : List Trace
  revisionSafe : ∀ link ∈ trace,
    link.sourceRevision = sourceRevision ∧ link.targetRevision = targetRevision target

end Synthesis.Interop
