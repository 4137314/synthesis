import Synthesis.Domains.Electronics.Element
import Synthesis.Domains.Electronics.Resistive
import Synthesis.Domains.Electronics.Network
import Synthesis.Domains.Electronics.Nodal
import Synthesis.Domains.Electronics.Source
import Synthesis.Domains.Electronics.Thevenin
import Synthesis.Domains.Electronics.Ode
import Synthesis.Domains.Electronics.Storage
import Synthesis.Domains.Electronics.Transient
import Synthesis.Domains.Electronics.SecondOrder
import Synthesis.Domains.Electronics.Rlc
import Synthesis.Domains.Electronics.Phasor
import Synthesis.Domains.Electronics.Power
import Synthesis.Domains.Electronics.Filter
import Synthesis.Domains.Electronics.TwoPort
import Synthesis.Domains.Electronics.Magnetics
import Synthesis.Domains.Electronics.Semiconductor
import Synthesis.Domains.Electronics.Feedback
import Synthesis.Domains.Electronics.Digital

/-! # Analytic electronics

Umbrella of the Mathlib layer of the electronics domain. Modules are separated by the
mathematical setting they need rather than by device family, so that a result is proved
once at the weakest hypotheses that support it: over an arbitrary ordered field where
only algebra is involved, over the reals where calculus is needed, and over the complex
numbers for the phasor description.

Nothing in this layer may enter an AST component parameter: schema 2 stores rational
literals, and real or complex coefficients need an explicit representation or
approximation contract that is not implemented. The exact rational elements that do carry
AST parameters are in `Synthesis.Domains.Electronics`.

## Structural layer

| Module | Setting | Content |
| --- | --- | --- |
| `Element` | ordered field | two-terminal elements as admissible operating sets, interconnection, passivity |
| `Resistive` | ordered field | closed forms of the resistive interconnections, dividers, bridge, delta-wye |
| `Network` | commutative ring | finite lumped topologies, Kirchhoff's laws, Tellegen's theorem |
| `Nodal` | ordered field | the nodal operator, superposition, uniqueness of the resistive solution |
| `Source` | ordered field | Thévenin driving point, maximum power transfer, efficiency |
| `Thevenin` | ordered field | affine one-ports, closure under interconnection, uniqueness of the equivalent |

## Time domain

| Module | Setting | Content |
| --- | --- | --- |
| `Ode` | reals | scalar linear differential equations, existence and uniqueness |
| `Storage` | reals | capacitor and inductor constitutive laws and energy theorems |
| `Transient` | reals | first-order relaxation, its closed form and its uniqueness |
| `SecondOrder` | reals | the damped relaxation, its three regimes and mode completeness |
| `Rlc` | reals | the series and parallel second-order circuits, derived from the element laws |

## Frequency domain

| Module | Setting | Content |
| --- | --- | --- |
| `Phasor` | complex | element impedances and the series resonant branch |
| `Power` | complex | instantaneous power decomposition, complex power and the power triangle |
| `Filter` | complex | first-order responses, half-power cutoff and roll-off |
| `TwoPort` | field | impedance, admittance and transmission descriptions and their conversions |
| `Magnetics` | ordered field | coupled inductors and the ideal transformer |

## Devices and logic

| Module | Setting | Content |
| --- | --- | --- |
| `Semiconductor` | reals | the Shockley diode and the square-law transistor |
| `Feedback` | reals | the memoryless feedback loop and operational amplifier configurations |
| `Digital` | reals, `Bool` | Boolean identities, static logic levels and complementary switching |
-/
