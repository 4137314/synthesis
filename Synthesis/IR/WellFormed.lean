import Synthesis.IR.AST

namespace Synthesis.IR

/-- Propositional specification independent of the executable connection checker. -/
def Connection.Compatible (t : Technology) (c : Connection) : Prop :=
  ∃ source target,
    t.port? c.source = some source ∧ t.port? c.target = some target ∧
    source.direction = .output ∧ target.direction = .input ∧ source.type = target.type

theorem Connection.valid_iff (t : Technology) (c : Connection) :
    c.valid t = true ↔ c.Compatible t := by
  cases hs : t.port? c.source <;> cases ht : t.port? c.target <;>
    simp [valid, Compatible, hs, ht, and_assoc]

/-- Every accepted graph edge resolves to ports with the specified direction and type. -/
theorem Validated.connections_compatible (graph : Validated) (connection : Connection)
    (member : connection ∈ graph.ast.connections) : connection.Compatible graph.ast := by
  have h := graph.structurallyValid
  simp only [Technology.valid, Bool.and_eq_true] at h
  exact (connection.valid_iff graph.ast).mp (List.all_eq_true.mp h.1.1.2 connection member)

end Synthesis.IR
