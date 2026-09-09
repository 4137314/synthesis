import Synthesis.Domains.Electronics.Exact.Resistor

namespace Synthesis.Domains.Electronics
open Physics
set_option autoImplicit false

/-! # Exact ideal independent sources

A source is an idealized boundary condition, not a passive element: it may deliver
energy, so no passivity theorem is available or claimed for it. Certificates built on
these definitions must carry an explicit operating-envelope assumption instead.

The only solved circuit in the exact layer lives here: a single ideal voltage source
loaded by one strictly positive resistance has exactly one operating point. Larger
topologies need the network layer under `Synthesis.Domains.Electronics.Network`. -/

/-- An ideal voltage source fixes its terminal voltage for every current. -/
structure VoltageSource where
  emf : Voltage

/-- An ideal current source fixes its branch current for every terminal voltage. -/
structure CurrentSource where
  drive : Current

/-- Power delivered by a source into the external circuit, in the active sign convention. -/
def VoltageSource.delivered (s : VoltageSource) (i : Current) : Power := ⟨s.emf.value * i.value⟩

def CurrentSource.delivered (s : CurrentSource) (v : Voltage) : Power := ⟨v.value * s.drive.value⟩

/-- Reversing the reference current reverses the delivered power: a source absorbs when
driven backwards, which is why it has no unconditional passivity theorem. -/
theorem VoltageSource.delivered_odd (s : VoltageSource) (i : Current) :
    (s.delivered ⟨-i.value⟩).value = -(s.delivered i).value := by
  simp only [VoltageSource.delivered]
  grind

theorem CurrentSource.delivered_odd (s : CurrentSource) (v : Voltage) :
    (s.delivered ⟨-v.value⟩).value = -(s.delivered v).value := by
  simp only [CurrentSource.delivered]
  grind

/-- A dead voltage source is a short circuit: it holds zero terminal voltage and
exchanges no power at any current. This is the source-killing step of superposition. -/
theorem VoltageSource.dead_delivers_nothing (i : Current) :
    (VoltageSource.delivered ⟨⟨0⟩⟩ i).value = 0 := by
  simp [VoltageSource.delivered]

/-- A dead current source is an open circuit. -/
theorem CurrentSource.dead_delivers_nothing (v : Voltage) :
    (CurrentSource.delivered ⟨⟨0⟩⟩ v).value = 0 := by
  simp [CurrentSource.delivered]

/-- The driving-point equation of a source loaded by one strictly positive resistance,
together with uniqueness of the operating point. This is a genuine solved circuit, not
only a consistency statement. -/
theorem source_loop_operating_point (s : VoltageSource) (r : Positive Dimension.resistance) :
    ∃ i : Current, s.emf.value = r.quantity.value * i.value ∧
      ∀ j : Current, s.emf.value = r.quantity.value * j.value → j.value = i.value := by
  have h := r.positive
  refine ⟨⟨s.emf.value / r.quantity.value⟩, by grind, ?_⟩
  intro j hj
  grind

/-- A loaded ideal source delivers exactly the power the load dissipates. -/
theorem source_power_balance (s : VoltageSource) (r : Resistor) (i : Current)
    (kvl : s.emf.value = (voltage r i).value) :
    (s.delivered i).value = (power r i).value := by
  simp only [VoltageSource.delivered, power]
  rw [kvl]

/-- The loaded source delivers nonnegative power, because the loop current it drives has
the sign of its electromotive force. This is the exact-layer form of the statement that
a resistively loaded source cannot be driven backwards. -/
theorem source_loaded_delivers (s : VoltageSource) (r : Resistor) (i : Current)
    (kvl : s.emf.value = (voltage r i).value) : 0 ≤ (s.delivered i).value := by
  rw [source_power_balance s r i kvl]
  exact passive r i

/-- The dual solved circuit: an ideal current source across a strictly positive
conductance has exactly one terminal voltage. -/
theorem source_node_operating_point (s : CurrentSource) (g : Positive Dimension.conductance) :
    ∃ v : Voltage, s.drive.value = g.quantity.value * v.value ∧
      ∀ w : Voltage, s.drive.value = g.quantity.value * w.value → w.value = v.value := by
  have h := g.positive
  refine ⟨⟨s.drive.value / g.quantity.value⟩, by grind, ?_⟩
  intro w hw
  grind

end Synthesis.Domains.Electronics
