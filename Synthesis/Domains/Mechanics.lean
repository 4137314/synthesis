import Synthesis.Physics.Rational

namespace Synthesis.Domains.Mechanics
open Physics
set_option autoImplicit false

/-- One-dimensional, small-strain, linear elastic material within its elastic regime. -/
abbrev ElasticMaterial := Positive Dimension.pressure
abbrev Strain := Quantity Rat Dimension.scalar
abbrev Stress := Quantity Rat Dimension.pressure

/-- Stress and energy density share dimensions but are distinct named observables here. -/
def stress (material : ElasticMaterial) (strain : Strain) : Stress :=
  ⟨material.quantity.value * strain.value⟩

def energyDensity (material : ElasticMaterial) (strain : Strain) : Quantity Rat Dimension.pressure :=
  ⟨(1 / 2 : Rat) * material.quantity.value * (strain.value * strain.value)⟩

theorem stress_dimensions : Dimension.pressure.mul Dimension.scalar = Dimension.pressure := by decide

theorem energy_nonnegative (material : ElasticMaterial) (strain : Strain) :
    0 ≤ (energyDensity material strain).value := by
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (by grind) (positive_nonnegative material))
    (square_nonnegative strain.value)

theorem stress_strictly_monotone (material : ElasticMaterial) (a b : Strain)
    (h : a.value < b.value) : (stress material a).value < (stress material b).value :=
  Rat.mul_lt_mul_of_pos_left h material.positive

theorem stress_unique (material : ElasticMaterial) (a b : Strain)
    (h : stress material a = stress material b) : a = b := by
  have hv := congrArg Quantity.value h
  simp only [stress] at hv
  have hm := material.positive
  have hab := Rat.le_of_mul_le_mul_left
    (show material.quantity.value * a.value ≤ material.quantity.value * b.value by
      rw [hv]; exact Rat.le_refl) hm
  have hba := Rat.le_of_mul_le_mul_left
    (show material.quantity.value * b.value ≤ material.quantity.value * a.value by
      rw [hv]; exact Rat.le_refl) hm
  have he : a.value = b.value := Rat.le_antisymm hab hba
  exact congrArg Quantity.mk he

theorem energy_even (material : ElasticMaterial) (strain : Strain) :
    energyDensity material ⟨-strain.value⟩ = energyDensity material strain := by
  apply congrArg Quantity.mk
  grind

theorem work_identity (material : ElasticMaterial) (strain : Strain) :
    2 * (energyDensity material strain).value = (stress material strain).value * strain.value := by
  simp only [energyDensity, stress]
  grind

end Synthesis.Domains.Mechanics
