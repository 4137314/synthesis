namespace Synthesis

/-- Lean source API release. Independent of schema and wire compatibility. -/
def apiVersion : String := "0.6.1"

/-- Generic interop contract protocol version; individual targets own their versions. -/
def interopVersion : Nat := 2

end Synthesis
