import Synthesis.IR.WellFormed

namespace Synthesis.IR
set_option autoImplicit false

abbrev Context := List (Symbol × TypeExpr)

/-- Explicit extension configuration, composed by ordinary Lean functions. `none`
is unsupported. Callbacks see complete data, including attributes and nested bodies. -/
structure Extension where
  type : TypeExpr → Bool
  literal : TypeExpr → Data → Bool
  /-- Original arguments permit value-dependent signatures such as statically sized slices. -/
  application : ContractId → List Term → List TypeExpr → Option TypeExpr
  port : Port → Bool
  junction : Module → Definition → Junction → Bool
  operation : Operation → Bool
  acceptAttribute : Attribute → Bool
  explain : Module → List Diagnostic := fun _ => []

mutual
  /-- An unrecognized expression never acquires a guessed result type. -/
  def Extension.infer (ext : Extension) (context : Context) : Term → Option TypeExpr
    | .literal ty value => if ty.constructor.valid && ext.type ty && ext.literal ty value then some ty else none
    | .variable name => (context.find? (·.1 == name)).map (·.2)
    | .apply op args => do
      if !op.valid then none else pure ()
      let types ← ext.inferList context args
      let result ← ext.application op args types
      if result.constructor.valid && ext.type result then some result else none
  termination_by structural term => term

  def Extension.inferList (ext : Extension) (context : Context) : List Term → Option (List TypeExpr)
    | [] => some []
    | term :: rest => do
      let ty ← ext.infer context term
      let tys ← ext.inferList context rest
      some (ty :: tys)
  termination_by structural terms => terms
end

def Extension.parameters (ext : Extension) : Context → List Parameter → Option Context
  | context, [] => some context
  | context, p :: ps => do
    if !p.type.constructor.valid || !ext.type p.type then none else do
      match p.value with
      | some term => if ext.infer context term != some p.type then none else pure ()
      | none => pure ()
      ext.parameters (context ++ [(p.name, p.type)]) ps

/-- Supplied bindings are unique and typed. Omitted values remain symbolic; concrete
parameter sufficiency is a separate consumer requirement. -/
def Extension.bindingsValid (ext : Extension) (context : Context)
    (parameters : List Parameter) (bindings : List Binding) : Bool :=
  namesValid (bindings.map (·.name)) &&
  bindings.all (fun b => parameters.any (fun p => p.name == b.name &&
    ext.infer context b.value == some p.type))

def Operation.results : Operation → List Parameter
  | .node _ _ _ results _ _ _ => results

mutual
  def Extension.operationValid (ext : Extension) (context : Context) : Operation → Bool
    | .node name contract args results attrs body provenance =>
      let op := Operation.node name contract args results attrs body provenance
      !name.text.isEmpty && contract.valid && ext.operation op &&
      args.all (fun t => (ext.infer context t).isSome) &&
      namesValid (results.map (·.name)) &&
      (results.map (·.name)).all (fun n => !(context.map (·.1)).contains n) &&
      attrs.all (fun a => a.contract.valid && ext.acceptAttribute a) &&
      match ext.parameters context results with
      | none => false
      | some nested => ext.operationsValid nested body
  termination_by structural op => op

  def Extension.operationsValid (ext : Extension) (context : Context) : List Operation → Bool
    | [] => true
    | op :: rest => ext.operationValid context op &&
      match ext.parameters context op.results with
      | none => false
      | some next => ext.operationsValid next rest
  termination_by structural ops => ops
end

def Extension.definitionValid (ext : Extension) (m : Module) (d : Definition) : Bool :=
  match ext.parameters [] d.parameters with
  | none => false
  | some context =>
    d.attributes.all (fun a => a.contract.valid && ext.acceptAttribute a) &&
    d.ports.all (fun p => p.interface.valid && p.role.valid && p.type.constructor.valid && ext.type p.type && ext.port p && p.attributes.all (fun a => a.contract.valid && ext.acceptAttribute a)) &&
    d.junctions.all (fun j => j.contract.valid && ext.junction m d j && j.attributes.all (fun a => a.contract.valid && ext.acceptAttribute a)) &&
    d.instances.all (fun i => i.attributes.all (fun a => a.contract.valid && ext.acceptAttribute a) &&
      match m.definition? i.definition with
      | none => false
      | some child => ext.bindingsValid context child.parameters i.bindings) &&
    ext.operationsValid (context ++ d.ports.map (fun p => (p.name, p.type))) d.operations

def Extension.accepts (ext : Extension) (m : Module) : Bool :=
  m.attributes.all (fun a => a.contract.valid && ext.acceptAttribute a) && m.definitions.all (ext.definitionValid m) &&
  match m.definition? m.root with
  | none => false
  | some root => ext.bindingsValid [] root.parameters m.bindings

/-- Extension typing evidence is tied to a particular extension configuration. It is
not semantic coverage and cannot establish the truth of a constraint operation. -/
structure Checked (ext : Extension) extends Validated where
  accepted : ext.accepts ast = true

def Extension.diagnostics (ext : Extension) (m : Module) : List Diagnostic :=
  ext.explain m ++ m.definitions.flatMap (fun d =>
    (if ext.definitionValid m d then [] else [{
      (Diagnostic.error "E-DEFINITION-TYPE" "Unsupported declaration, expression, attribute or parameter binding.") with
      scope := some d.id, source := d.provenance.source }]) ++
    d.ports.filterMap (fun p => if ext.type p.type && ext.port p then none else some {
      (Diagnostic.error "E-PORT-TYPE" "Port type, role or interface is unsupported.") with
      scope := some d.id, entity := some p.name,
      actual := some (.tagged p.type.constructor p.type.arguments) }) ++
    d.junctions.filterMap (fun j => if ext.junction m d j then none else some {
      (Diagnostic.error "E-CONNECT" "Connector contract rejected this endpoint set or its ownership.") with
      scope := some d.id, entity := some j.name, source := j.provenance.source,
      expected := some (.tagged j.contract []),
      actual := some (.sequence (j.endpoints.map fun e =>
        match m.port? d e with
        | none => .symbol e.port
        | some p => .tagged p.interface [.tagged p.type.constructor p.type.arguments])),
      remediation := some "Check connector roles, resource incidence and types; cross-domain coupling requires an explicit bridge." }))

def Extension.check (ext : Extension) (m : Module) : Except (List Diagnostic) (Checked ext) :=
  if hs : m.Structural then
    if h : ext.accepts m = true then .ok ⟨⟨m, hs⟩, h⟩
    else .error (Diagnostic.error "E-EXTENSION" "Extension checking failed; inspect declaration diagnostics and root bindings."
      :: ext.diagnostics m)
  else .error m.diagnostics

end Synthesis.IR
