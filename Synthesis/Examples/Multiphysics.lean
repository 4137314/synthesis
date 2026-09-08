import Synthesis.Frontend.Compile

namespace Synthesis.Examples
open IR Frontend

/-- An explicit electro-optic interface. Operation names denote contracts to be defined
by a domain library; this example does not assert a device physics model. -/
def electroOptic : Design := {
  name := "electro-optic-modulator"
  components := [
    ⟨"driver", "synthesis.electronics.voltage-source", [
      ⟨"voltage", .output, .quantity .electronics .voltage⟩], []⟩,
    ⟨"modulator", "synthesis.photonics.electro-optic", [
      ⟨"drive", .input, .quantity .electronics .voltage⟩,
      ⟨"light", .output, .quantity .photonics .scalar⟩], []⟩,
    ⟨"receiver", "synthesis.photonics.receiver", [
      ⟨"light", .input, .quantity .photonics .scalar⟩], []⟩]
  connections := [
    ⟨⟨"driver", "voltage"⟩, ⟨"modulator", "drive"⟩⟩,
    ⟨⟨"modulator", "light"⟩, ⟨"receiver", "light"⟩⟩]
}

example : electroOptic.lower.valid = true := by decide

end Synthesis.Examples
