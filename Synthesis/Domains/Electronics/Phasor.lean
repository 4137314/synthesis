import Synthesis.Domains.Electronics.Phasor.Impedance
import Synthesis.Domains.Electronics.Phasor.Resonance

/-! # Sinusoidal steady state

Umbrella of the phasor description. At a fixed angular frequency a linear time-invariant
element is a complex impedance, and the time-domain reading of a phasor is fixed by
`phasor_time_domain`.

The model presupposes a single angular frequency, linearity and that transients have
decayed. It says nothing about start-up, large-signal behaviour or distortion, and it
must not be applied to a nonlinear element.

| Module | Content |
| --- | --- |
| `Phasor.Impedance` | element impedances, series and parallel combination, average power and the time-domain reading |
| `Phasor.Resonance` | the series resonant branch, its resonance frequency, impedance minimum and quality factor |
-/
