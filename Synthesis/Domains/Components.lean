import Synthesis.Domains.Adapters.Electronics
import Synthesis.Domains.Adapters.Thermal
import Synthesis.Domains.Adapters.Mechanics
import Synthesis.Domains.Adapters.Photonics
import Synthesis.Domains.Adapters.Quantum
import Synthesis.Domains.Adapters.Chemistry

/-! Convenience umbrella for independent domain adapters. No registry or dispatch table
is maintained here; consumers may import an individual Adapters module. -/
