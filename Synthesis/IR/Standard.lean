import Synthesis.IR.Extension

namespace Synthesis.IR.Standard
set_option autoImplicit false

/-- Small standard data contracts; external packages freely define other constructors. -/
def rational : TypeExpr := ⟨.named "synthesis.scalar" "rational", []⟩
def boolean : TypeExpr := ⟨.named "synthesis.scalar" "boolean", []⟩
def dimensions (d : Dimension) : Data := .sequence
  ([d.length, d.mass, d.time, d.current, d.temperature, d.amount, d.luminosity].map Data.integer)
def quantity (kind : ContractId) (dimension : Dimension) (scalar : TypeExpr := rational) : TypeExpr :=
  ⟨.named "synthesis.physics" "quantity", [.tagged kind [dimensions dimension],
    .tagged scalar.constructor scalar.arguments]⟩

def rationalParameter (name : String) (dimension : Dimension) (value : Rat) : Parameter :=
  let ty := quantity (.named "synthesis.parameter" name) dimension
  ⟨⟨name⟩, ty, some (.literal ty (.rational value))⟩

/-- An observed variable in a relation is neither a signal nor an acausal terminal. -/
def observable (owner name : String) (dimension : Dimension) : Port :=
  ⟨⟨name⟩, .named owner "observation", quantity (.named owner name) dimension,
    .named "synthesis.relation" "observable", []⟩

/-- A contract application may reference an external law or contain explicit term bodies. -/
def relation (name : String) (contract : ContractId) (arguments : List Term := []) : Operation :=
  .node ⟨name⟩ contract arguments [] [] [] {}

end Synthesis.IR.Standard
