import Synthesis.Domains.Electronics.Semiconductor.Diode
import Synthesis.Domains.Electronics.Semiconductor.Mosfet

/-! # Nonlinear device models

Umbrella of the two standard large-signal device equations. Both are static, isothermal
and single-device, and both are stated in coherent SI units.

| Module | Content |
| --- | --- |
| `Semiconductor.Diode` | the Shockley equation, its monotonicity, passivity, inverse and small-signal conductance |
| `Semiconductor.Mosfet` | the square-law transistor, pinch-off continuity and the transconductance identity |
-/
