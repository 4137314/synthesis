import Lean
import Synthesis.Frontend.Builder

namespace Synthesis.Frontend
set_option autoImplicit false

def hierarchy (m : IR.Module) : List (QualifiedId × List (Symbol × QualifiedId)) :=
  m.definitions.map fun d => (d.id, d.instances.map fun i => (i.name, i.definition))

def interfaces (m : IR.Module) : List (QualifiedId × List IR.Port) :=
  m.definitions.map fun d => (d.id, d.ports)

def operations (m : IR.Module) : List (QualifiedId × List IR.Operation) :=
  m.definitions.map fun d => (d.id, d.operations)

syntax "#engineering.check " term : command
macro_rules
  | `(#engineering.check $m) =>
    `(example : ($m : Synthesis.IR.Module).Structural := by constructor <;> decide +kernel)

syntax "#engineering.ir " term : command
syntax "#engineering.hierarchy " term : command
syntax "#engineering.interfaces " term : command
syntax "#engineering.operations " term : command
syntax "#engineering.diagnostics " term : command
macro_rules
  | `(#engineering.ir $m) => `(#eval repr ($m : Synthesis.IR.Module))
  | `(#engineering.hierarchy $m) => `(#eval repr (Synthesis.Frontend.hierarchy $m))
  | `(#engineering.interfaces $m) => `(#eval repr (Synthesis.Frontend.interfaces $m))
  | `(#engineering.operations $m) => `(#eval repr (Synthesis.Frontend.operations $m))
  | `(#engineering.diagnostics $m) => `(#eval repr (Synthesis.IR.Module.diagnostics $m))

end Synthesis.Frontend
