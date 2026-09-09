import Synthesis.IR.Extension

namespace Synthesis.IR.Connector
set_option autoImplicit false

/-- Complete resolved endpoint list; unknown references fail closed. -/
def ports? (m : Module) (d : Definition) (j : Junction) : Option (List Port) :=
  j.endpoints.mapM (m.port? d)

/-- Equality of declared interfaces is a typing rule, never a physical coupling law. -/
def homogeneous (ports : List Port) : Bool :=
  match ports with
  | [] => false
  | p :: rest => rest.all (fun q => q.interface == p.interface && q.type == p.type)

/-- Each endpoint is owned by at most one local net. A multiway net represents fanout. -/
def exclusive (d : Definition) (j : Junction) : Bool :=
  j.endpoints.all fun e =>
    (d.junctions.filter (fun other => other.endpoints.contains e)).length == 1

def signal (source sink : ContractId) (m : Module) (d : Definition) (j : Junction) : Bool :=
  match ports? m d j with
  | none => false
  | some ps => homogeneous ps && exclusive d j && ps.length > 1 &&
    (ps.filter (·.role == source)).length == 1 &&
    ps.all (fun p => p.role == source || p.role == sink)

/-- A resource connector forbids fanout, duplicate consumers and multiple ownership. -/
def resource (produce consume : ContractId) (m : Module) (d : Definition) (j : Junction) : Bool :=
  signal produce consume m d j && j.endpoints.length == 2

/-- Acausal terminals have no source/sink. Orientation is part of the chosen contract. -/
def conservative (terminal : ContractId) (m : Module) (d : Definition) (j : Junction) : Bool :=
  match ports? m d j with
  | none => false
  | some ps => homogeneous ps && exclusive d j && ps.length > 1 &&
    ps.all (·.role == terminal)

end Synthesis.IR.Connector
