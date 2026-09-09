import Synthesis.Domains.Electronics.Element.Basic
import Synthesis.Domains.Electronics.Element.Interconnect
import Synthesis.Domains.Electronics.Element.Passivity

/-! # Two-terminal element theory

Umbrella of the relational element model. A two-terminal element is the set of terminal
pairs `(v, i)` it admits at a fixed operating point, which is the representation ideal
sources require: they are not functions of their terminal variables.

| Module | Content |
| --- | --- |
| `Element.Basic` | the admissible-set representation, terminal equivalence, the element catalog, feasibility and the dual parameterizations |
| `Element.Interconnect` | series and parallel composition and their structural laws |
| `Element.Passivity` | passivity and losslessness, their characterizations and their transport along equivalence and interconnection |
-/
