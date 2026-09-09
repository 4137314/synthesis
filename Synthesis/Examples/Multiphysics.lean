import Synthesis.Frontend.Builder
import Synthesis.IR.Standard

namespace Synthesis.Examples
open IR Frontend
set_option autoImplicit false

/-- Explicit bridge interface. This example claims structure, not coupling physics. -/
def electroOpticBridge : Definition := engineering ⟨["examples", "electro-optic"]⟩ where
  port (Standard.observable "electrical" "drive" .voltage)
  port (Standard.observable "optical" "power" .power)
  operation (Standard.relation "coupling" (.named "examples" "electro-optic-law"))

def electroOptic : Module := design (engineering ⟨["examples", "system"]⟩ where
  instanceOf "left" electroOpticBridge.id
  instanceOf "right" electroOpticBridge.id) [electroOpticBridge]

example : electroOptic.Structural := by constructor <;> decide

end Synthesis.Examples
