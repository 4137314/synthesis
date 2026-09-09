import Synthesis.Domains.Electronics.Digital.Gate
import Synthesis.Domains.Electronics.Digital.Level
import Synthesis.Domains.Electronics.Digital.Cmos

/-! # Digital logic

Umbrella of three deliberately separate models: what a gate computes, the electrical
discipline that lets a continuous voltage stand for a Boolean value, and the ideal
switching behaviour of a complementary pair.

None of them has time in it. Propagation delay, transition time, dynamic power,
metastability and race conditions are outside all three, and no theorem here establishes
that a physical gate network settles or is free of hazards.

| Module | Content |
| --- | --- |
| `Digital.Gate` | Boolean identities, functional completeness of `nand`, full-adder correctness |
| `Digital.Level` | static level discipline, noise margins, level restoration and noise immunity |
| `Digital.Cmos` | ideal complementary switching and the absence of a static crowbar path |
-/
