import Synthesis.Design.System
import Synthesis.Frontend.Elaborate

namespace Synthesis.Frontend
set_option autoImplicit false
universe u
variable {Global Local : Type u}

abbrev SystemBuilder (Global : Type u) := StateM (Design.System Global)

/-- Typed component composition infers the local observation type from its model. -/
def place (name : Symbol) (model : Semantics.Model Local) (observe : Global → Local) :
    SystemBuilder Global PUnit := modify fun system =>
  { system with parts := system.parts ++ [⟨name, Local, model, observe⟩] }

def couple (junction : IR.Junction) (relation : Logic.Behavior Global) : SystemBuilder Global PUnit :=
  modify fun system => { system with couplings := system.couplings ++ [⟨junction, relation⟩] }

def constrain (declaration : IR.Operation) (relation : Logic.Behavior Global) : SystemBuilder Global PUnit :=
  modify fun system => { system with constraints := system.constraints ++ [⟨declaration, relation⟩] }

def require (requirement : Design.Requirement Global) : SystemBuilder Global PUnit :=
  modify fun system => { system with requirements := system.requirements ++ [requirement] }

def system (id : QualifiedId) (body : SystemBuilder Global PUnit) : Design.System Global :=
  (body.run { id := id }).2

def compileSystem (source : Design.System Global) := compileModel source.represented

theorem compileSystem_preserves (source : Design.System Global) (model : Semantics.Model Global)
    (h : compileSystem source = .ok model) : ∀ x, model.behavior x ↔ source.behavior x :=
  compileModel_preserves source.represented model h

syntax "engineering_system " term " where " doSeq : term
macro_rules
  | `(engineering_system $id where $body:doSeq) =>
    `(Synthesis.Frontend.system $id (do $body))

end Synthesis.Frontend
