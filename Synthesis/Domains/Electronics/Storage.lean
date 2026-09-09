import Synthesis.Domains.Electronics.Storage.Capacitor
import Synthesis.Domains.Electronics.Storage.Inductor

/-! # Energy storage in continuous time

Umbrella of the two reactive elements. Each is defined by its differential constitutive
relation over real time, and each carries the energy theorem that identifies absorbed
power with the derivative of a stored state function.

| Module | Content |
| --- | --- |
| `Storage.Capacitor` | `i = dq/dt`, electrostatic energy, the parallel law, charge and energy integrals |
| `Storage.Inductor` | `v = dφ/dt`, magnetic energy, the series law and the energy integral |
-/
