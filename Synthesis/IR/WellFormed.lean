import Synthesis.IR.Diagnostic

namespace Synthesis.IR
set_option autoImplicit false

def unique {α : Type} [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

def namesValid (xs : List Symbol) : Bool :=
  xs.all (fun x => !x.text.isEmpty) && unique xs

def qualifiedValid (id : QualifiedId) : Bool :=
  !id.segments.isEmpty && id.segments.all (!·.isEmpty)

/-- Finite hierarchy is required. Fuel is bounded by the number of distinct definitions. -/
def Module.acyclic (m : Module) : Nat → Definition → Bool
  | 0, _ => false
  | fuel + 1, d => d.instances.all fun i =>
    match m.definition? i.definition with
    | none => false
    | some child => m.acyclic fuel child

mutual
  def Operation.identitiesValid : Operation → Bool
    | .node name _ _ results _ body _ =>
      !name.text.isEmpty && namesValid (results.map (·.name)) &&
      namesValid (body.map (·.name)) && operationIdentities body
  termination_by structural op => op

  def operationIdentities : List Operation → Bool
    | [] => true
    | op :: rest => op.identitiesValid && operationIdentities rest
  termination_by structural ops => ops
end

def Definition.identitiesValid (d : Definition) : Bool :=
  qualifiedValid d.id && namesValid (d.parameters.map (·.name)) &&
  namesValid (d.ports.map (·.name)) && namesValid (d.instances.map (·.name)) &&
  namesValid (d.junctions.map (·.name)) && namesValid (d.operations.map (·.name)) &&
  d.instances.all (fun i => namesValid (i.bindings.map (·.name))) &&
  namesValid ((d.parameters.map (·.name)) ++ (d.ports.map (·.name))) &&
  operationIdentities d.operations

def Module.identitiesValid (m : Module) : Bool :=
  m.schema == schemaVersion && unique (m.definitions.map (·.id)) && m.definitions.all Definition.identitiesValid &&
  namesValid (m.bindings.map (·.name))

def Module.referencesValid (m : Module) : Bool :=
  (m.definition? m.root).isSome && m.definitions.all (fun d =>
    m.acyclic (m.definitions.length + 1) d &&
    d.junctions.all (fun j => !j.endpoints.isEmpty && unique j.endpoints &&
      j.endpoints.all (fun e => (m.port? d e).isSome)))

/-- Structural specifications deliberately do not assert physical or extension validity. -/
def Module.Structural (m : Module) : Prop :=
  m.identitiesValid = true ∧ m.referencesValid = true

def Module.summary (m : Module) : List Diagnostic :=
  (if m.identitiesValid then [] else
    [Diagnostic.error "E-IDENTITY" "Unsupported schema version or empty/duplicate identity in a declaration scope."]) ++
  (if m.referencesValid then [] else
    [Diagnostic.error "E-REFERENCE" "Unresolved root/endpoint, duplicate endpoint, or recursive hierarchy."])

theorem Module.summary_iff (m : Module) :
    m.summary = [] ↔ m.Structural := by
  simp [summary, Structural]

structure Validated where
  ast : Module
  structurallyValid : ast.Structural

instance (m : Module) : Decidable m.Structural := inferInstanceAs
  (Decidable (m.identitiesValid = true ∧ m.referencesValid = true))

/-- Detailed resolution diagnostics preserve the containing definition and source span. -/
def Module.details (m : Module) : List Diagnostic :=
  m.definitions.flatMap fun d =>
    (if d.identitiesValid then [] else [{
      (Diagnostic.error "E-SCOPE" "Empty, duplicate or shadowed declaration identity.") with
      scope := some d.id, source := d.provenance.source }]) ++
    (if m.acyclic (m.definitions.length + 1) d then [] else [{
      (Diagnostic.error "E-HIERARCHY" "Missing definition or recursive instance hierarchy.") with
      scope := some d.id, source := d.provenance.source,
      remediation := some "Resolve instance definitions; represent dynamic recurrence in behavior." }]) ++
    d.junctions.flatMap (fun j => j.endpoints.filterMap fun e =>
      if (m.port? d e).isSome then none else some {
        (Diagnostic.error "E-ENDPOINT" "Endpoint does not resolve in this instance scope.") with
        scope := some d.id, entity := some j.name, source := j.provenance.source,
        actual := some (.sequence ((e.path ++ [e.port]).map Data.symbol)),
        remediation := some "Declare the instance path and port, or correct the reference." })

def Module.diagnostics (m : Module) : List Diagnostic :=
  if m.Structural then [] else m.summary ++ m.details

theorem Module.diagnostics_iff (m : Module) : m.diagnostics = [] ↔ m.Structural := by
  by_cases h : m.Structural
  · simp [diagnostics, h]
  · have hs : m.summary ≠ [] := fun he => h ((m.summary_iff).mp he)
    simp [diagnostics, h, hs]

def validate (m : Module) : Except (List Diagnostic) Validated :=
  if h : m.Structural then .ok ⟨m, h⟩ else .error m.diagnostics

/-- Resolution is guaranteed for every accepted junction endpoint. -/
theorem Validated.endpoints_resolve (v : Validated) (d : Definition)
    (hd : d ∈ v.ast.definitions) (j : Junction) (hj : j ∈ d.junctions)
    (e : Endpoint) (he : e ∈ j.endpoints) : ∃ p, v.ast.port? d e = some p := by
  have h := v.structurallyValid.2
  simp only [Module.referencesValid, Bool.and_eq_true] at h
  have h := List.all_eq_true.mp h.2 d hd
  simp only [Bool.and_eq_true] at h
  have h := List.all_eq_true.mp h.2 j hj
  simp only [Bool.and_eq_true] at h
  have h := List.all_eq_true.mp h.2 e he
  cases hp : v.ast.port? d e with
  | none => simp [hp] at h
  | some p => exact ⟨p, rfl⟩

end Synthesis.IR
