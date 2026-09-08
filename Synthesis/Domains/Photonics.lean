import Synthesis.Physics.Rational

namespace Synthesis.Domains.Photonics
open Physics
set_option autoImplicit false

/-- Incoherent single-input power-budget model at a fixed operating point. -/
structure Splitter where
  transmittedFraction : Rat
  reflectedFraction : Rat
  transmitted_nonnegative : 0 ≤ transmittedFraction
  reflected_nonnegative : 0 ≤ reflectedFraction
  passive : transmittedFraction + reflectedFraction ≤ 1

abbrev OpticalPower := Nonnegative Dimension.power

def transmitted (s : Splitter) (input : OpticalPower) : Quantity Rat Dimension.power :=
  ⟨s.transmittedFraction * input.quantity.value⟩

def reflected (s : Splitter) (input : OpticalPower) : Quantity Rat Dimension.power :=
  ⟨s.reflectedFraction * input.quantity.value⟩

def absorbed (s : Splitter) (input : OpticalPower) : Quantity Rat Dimension.power :=
  ⟨(1 - s.transmittedFraction - s.reflectedFraction) * input.quantity.value⟩

theorem transmitted_nonnegative (s : Splitter) (input : OpticalPower) :
    0 ≤ (transmitted s input).value :=
  Rat.mul_nonneg s.transmitted_nonnegative input.nonnegative

theorem reflected_nonnegative (s : Splitter) (input : OpticalPower) :
    0 ≤ (reflected s input).value :=
  Rat.mul_nonneg s.reflected_nonnegative input.nonnegative

theorem absorbed_nonnegative (s : Splitter) (input : OpticalPower) :
    0 ≤ (absorbed s input).value := by
  apply Rat.mul_nonneg _ input.nonnegative
  have h := s.passive
  grind

theorem power_conservation (s : Splitter) (input : OpticalPower) :
    (transmitted s input).value + (reflected s input).value + (absorbed s input).value =
      input.quantity.value := by
  simp only [transmitted, reflected, absorbed]
  grind

theorem no_gain (s : Splitter) (input : OpticalPower) :
    (transmitted s input).value + (reflected s input).value ≤ input.quantity.value := by
  have h := absorbed_nonnegative s input
  have hc := power_conservation s input
  grind

theorem lossless (s : Splitter) (input : OpticalPower)
    (h : s.transmittedFraction + s.reflectedFraction = 1) : (absorbed s input).value = 0 := by
  simp only [absorbed]
  grind

end Synthesis.Domains.Photonics
