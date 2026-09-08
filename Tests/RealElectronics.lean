import Synthesis.Domains.RealElectronics

namespace Tests.RealElectronics
open Synthesis Synthesis.Domains.RealElectronics
set_option autoImplicit false

/-- Real-valued proofs are compiled and audited without linking Mathlib into the
small executable used for runtime frontend regressions. -/
example (r : Resistor) (i : Current) : 0 ≤ (power r i).value := passive r i

example (a b : Resistor) (i : Current) :
    (power (series a b) i).value = (power a i).value + (power b i).value := series_power a b i

example : ¬(((-1 : ℝ) * (2 : ℝ)) * 2 ≥ 0) := by norm_num

end Tests.RealElectronics
