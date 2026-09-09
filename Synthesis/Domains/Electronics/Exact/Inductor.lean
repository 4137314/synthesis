import Synthesis.Domains.Electronics.Exact.Units

namespace Synthesis.Domains.Electronics
open Physics
set_option autoImplicit false

/-! # Exact inductive storage

The flux linkage and energy state functions of an ideal linear inductor at a fixed
branch current, together with the series combination law. This is the dual of
`Synthesis.Domains.Electronics.Exact.Capacitor`.

Faraday's law `v = dφ/dt` needs continuous time and lives in
`Synthesis.Domains.Electronics.Storage`. Winding resistance, core loss, saturation,
hysteresis and mutual coupling are not modelled here; coupled windings have their own
model in `Synthesis.Domains.Electronics.Magnetics`. -/

/-- Flux linkage of an ideal linear inductor carrying current `i`. -/
def flux (l : Inductor) (i : Current) : Flux := ⟨l.quantity.value * i.value⟩

/-- Magnetic energy `L i² / 2`, a state function of the branch current. -/
def inductiveEnergy (l : Inductor) (i : Current) : Energy :=
  ⟨l.quantity.value * (i.value * i.value) / 2⟩

theorem flux_additive (l : Inductor) (i j : Current) :
    (flux l ⟨i.value + j.value⟩).value = (flux l i).value + (flux l j).value := by
  simp only [flux]
  grind

theorem flux_zero (l : Inductor) : (flux l ⟨0⟩).value = 0 := by simp [flux]

/-- Flux linkage determines the branch current: this is why zero inductance is excluded
from the parameter type. -/
theorem flux_injective (l : Inductor) (i j : Current)
    (equal : (flux l i).value = (flux l j).value) : i.value = j.value := by
  have nonzero : l.quantity.value ≠ 0 := by have := l.positive; grind
  simp only [flux] at equal
  have factored : l.quantity.value * (i.value - j.value) = 0 := by grind
  rcases Rat.mul_eq_zero.mp factored with degenerate | difference
  · exact absurd degenerate nonzero
  · grind

theorem inductive_energy_nonnegative (l : Inductor) (i : Current) :
    0 ≤ (inductiveEnergy l i).value := by
  have := Rat.mul_nonneg (positive_nonnegative l) (square_nonnegative i.value)
  simp only [inductiveEnergy]
  grind

theorem inductive_energy_even (l : Inductor) (i : Current) :
    (inductiveEnergy l ⟨-i.value⟩).value = (inductiveEnergy l i).value := by
  simp only [inductiveEnergy]
  grind

theorem inductive_energy_flux (l : Inductor) (i : Current) :
    2 * l.quantity.value * (inductiveEnergy l i).value = (flux l i).value * (flux l i).value := by
  simp only [inductiveEnergy, flux]
  grind

theorem inductive_energy_zero_iff (l : Inductor) (i : Current) :
    (inductiveEnergy l i).value = 0 ↔ i.value = 0 := by
  have h := l.positive
  simp only [inductiveEnergy]
  constructor
  · intro hzero
    grind
  · intro hzero
    grind

/-- Inductances add in series, where both elements carry the same branch current. -/
def seriesInductance (a b : Inductor) : Inductor :=
  ⟨⟨a.quantity.value + b.quantity.value⟩, by
    have ha := a.positive
    have hb := b.positive
    grind⟩

theorem series_flux (a b : Inductor) (i : Current) :
    (flux (seriesInductance a b) i).value = (flux a i).value + (flux b i).value := by
  simp only [flux, seriesInductance]
  grind

theorem series_inductive_energy (a b : Inductor) (i : Current) :
    (inductiveEnergy (seriesInductance a b) i).value =
      (inductiveEnergy a i).value + (inductiveEnergy b i).value := by
  simp only [inductiveEnergy, seriesInductance]
  grind

theorem series_inductance_comm (a b : Inductor) :
    (seriesInductance a b).quantity.value = (seriesInductance b a).quantity.value := by
  simp only [seriesInductance]
  grind

theorem series_inductance_assoc (a b c : Inductor) :
    (seriesInductance (seriesInductance a b) c).quantity.value =
      (seriesInductance a (seriesInductance b c)).quantity.value := by
  simp only [seriesInductance]
  grind

/-- Reluctance-like reciprocal inductance, the parameter that makes the parallel
inductance law additive. -/
def inverseInductance (l : Inductor) : Positive (Dimension.inductance.inv) :=
  ⟨⟨1 / l.quantity.value⟩, reciprocal_positive l.positive⟩

theorem inverse_inductance_product (l : Inductor) :
    l.quantity.value * (inverseInductance l).quantity.value = 1 :=
  Physics.reciprocal_product l.positive

/-- Parallel inductors share the terminal flux linkage; their reciprocal inductances
add. This is the division-free statement of the parallel inductance law. -/
theorem parallel_inductor_current (a b : Inductor) (φ : Flux) (ia ib : Current)
    (fluxA : φ.value = (flux a ia).value) (fluxB : φ.value = (flux b ib).value) :
    ia.value + ib.value =
      φ.value * ((inverseInductance a).quantity.value + (inverseInductance b).quantity.value) := by
  have ha := inverse_inductance_product a
  have hb := inverse_inductance_product b
  simp only [flux] at fluxA fluxB
  grind

end Synthesis.Domains.Electronics
