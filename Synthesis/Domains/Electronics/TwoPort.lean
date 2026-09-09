import Synthesis.Domains.Electronics.TwoPort.Impedance
import Synthesis.Domains.Electronics.TwoPort.Admittance
import Synthesis.Domains.Electronics.TwoPort.Transmission
import Synthesis.Domains.Electronics.TwoPort.Conversion

/-! # Two-port networks

Umbrella of the two-port descriptions. Each description is a different coordinate system
on the same object, and each has its own module because each has a different natural
algebra: impedance parameters add under series-series interconnection, admittance
parameters add under parallel-parallel interconnection, and transmission parameters
multiply under cascading.

The changes of coordinates are partial and their nondegeneracy conditions are explicit;
`Conversion` proves each one correct at the terminals rather than assuming that the
matrices invert.

| Module | Content |
| --- | --- |
| `TwoPort.Impedance` | impedance parameters, the port quadratic form, passivity as definiteness, the T realization and the loaded input impedance |
| `TwoPort.Admittance` | admittance parameters, parallel-parallel composition, the Π realization and the dual passivity characterization |
| `TwoPort.Transmission` | transmission parameters, cascade composition, the determinant identity and its preservation |
| `TwoPort.Conversion` | impedance/admittance/transmission conversions, their nondegeneracy conditions, round trips and the agreement of the two notions of reciprocity |
-/
