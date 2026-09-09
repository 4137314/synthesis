import Synthesis
import Synthesis.Domains
import Synthesis.Bridges

namespace Tests.Electronics
open Synthesis Synthesis.Physics Synthesis.Domains Synthesis.Semantics
set_option autoImplicit false

/-! Regression checks for the terminal, interconnection and network layers: the
two-terminal element algebra over the exact rationals, Kirchhoff's laws on a concrete
topology, the resistive closed forms, and the driving-point behaviour of a source. A
current assignment violating Kirchhoff's law and an unbalanced bridge are rejected. -/

/-! ## Two-terminal element algebra over the exact rationals -/

open Electronics.Element.TwoTerminal

example : Passive (resistor (10 : Rat)) := (resistor_passive_iff 10).mpr (by norm_num)

example : ¬Passive (resistor (-1 : Rat)) := by
  intro h
  have := (resistor_passive_iff (-1 : Rat)).mp h
  norm_num at this

example : ¬Passive (voltageSource (5 : Rat)) := voltage_source_not_passive (by norm_num)

example : Equivalent (series (resistor (3 : Rat)) (resistor 4)) (resistor 7) := by
  have combined := series_resistor (3 : Rat) 4
  norm_num at combined
  exact combined

example : Equivalent (thevenin (10 : Rat) 5) (norton 2 (1 / 5 : Rat)) := by
  have equivalence := thevenin_norton (e := (10 : Rat)) (r := 5) (by norm_num)
  norm_num at equivalence
  exact equivalence

/-! ## Interconnection laws -/

/-- Two branches between two nodes, oriented in opposite directions. -/
def loop : Electronics.Network.Topology (Fin 2) (Fin 2) :=
  ⟨fun b => if b = 0 then 0 else 1, fun b => if b = 0 then 1 else 0⟩

def potential : Fin 2 → Rat := fun n => if n = 0 then 5 else 0

def loopCurrent : Fin 2 → Rat := fun _ => 2

example : Electronics.Network.KCL loop loopCurrent := by
  intro n
  fin_cases n <;>
    norm_num [Electronics.Network.injection, Electronics.Network.incidence, loop, loopCurrent,
      Fin.sum_univ_two]

-- Tellegen's theorem on a concrete interconnection: the branch powers cancel exactly.
example : ∑ b, Electronics.Network.branchVoltage loop potential b * loopCurrent b = 0 := by
  refine Electronics.Network.tellegen loop potential loopCurrent ?_
  intro n
  fin_cases n <;>
    norm_num [Electronics.Network.injection, Electronics.Network.incidence, loop, loopCurrent,
      Fin.sum_univ_two]

-- A current assignment that violates Kirchhoff's law is rejected.
example : ¬Electronics.Network.KCL loop (fun b => if b = 0 then (2 : Rat) else 3) := by
  intro kcl
  have node := kcl 0
  norm_num [Electronics.Network.injection, Electronics.Network.incidence, loop,
    Fin.sum_univ_two] at node

/-! ## Resistive interconnection, sources and transfer -/

example : Electronics.Resistive.parallel (6 : Rat) 3 = 2 := by
  norm_num [Electronics.Resistive.parallel]

example : Electronics.Resistive.dividerVoltage (1 : Rat) 3 8 = 6 := by
  norm_num [Electronics.Resistive.dividerVoltage]

example : Electronics.Resistive.bridge (2 : Rat) 4 3 6 12 = 0 :=
  (Electronics.Resistive.bridge_balanced_iff (r1 := (2 : Rat)) (r2 := 4) (r3 := 3) (r4 := 6) (vin := 12)
    (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)

example : Electronics.Resistive.bridge (2 : Rat) 4 3 5 12 ≠ 0 := by
  intro balanced
  have condition := (Electronics.Resistive.bridge_balanced_iff (r1 := (2 : Rat)) (r2 := 4) (r3 := 3) (r4 := 5)
    (vin := 12) (by norm_num) (by norm_num) (by norm_num)).mp balanced
  norm_num at condition

example : Electronics.Source.loadPower (10 : ℝ) 5 5 = 5 := by
  rw [Electronics.Source.matched_load_power (by norm_num)]
  norm_num

example (load : ℝ) (external : 0 ≤ load) :
    Electronics.Source.loadPower (10 : ℝ) 5 load ≤ 5 := by
  have bound := Electronics.Source.maximum_power_transfer (e := (10 : ℝ)) (r := 5) (by norm_num) external
  norm_num at bound
  exact bound

example : Electronics.Source.efficiency (5 : ℝ) 5 = 1 / 2 :=
  Electronics.Source.matched_efficiency (by norm_num)

/-! ## Thevenin equivalence of a one-port -/

open Electronics.Thevenin

-- Series composition adds electromotive forces and internal resistances.
example : Equivalent (series (affine (5 : Rat) 2) (affine 3 4)) (affine (5 + 3) (2 + 4)) :=
  affine_series 5 2 3 4

-- Parallel composition combines the branches by the Millman form.
example : Equivalent (parallel (affine (6 : Rat) 2) (affine 3 1))
    (affine ((6 * 1 + 3 * 2) / (2 + 1)) (2 * 1 / (2 + 1))) :=
  affine_parallel (by norm_num) (by norm_num) (by norm_num)

example : ((6 : Rat) * 1 + 3 * 2) / (2 + 1) = 4 := by norm_num

example : (2 : Rat) * 1 / (2 + 1) = 2 / 3 := by norm_num

-- The equivalent is determined by the open-circuit voltage and the terminal slope.
example {e r f s : Rat} (indistinguishable : Equivalent (affine e r) (affine f s)) :
    e = f ∧ r = s := affine_unique indistinguishable

-- An affine one-port with a live source is never passive.
example : ¬Passive (affine (5 : Rat) 2) := affine_not_passive (by norm_num)

-- With a dead source it is an ordinary resistor and is passive.
example : Passive (affine (0 : Rat) 2) := affine_passive_iff.mpr ⟨rfl, by norm_num⟩

-- A negative internal resistance is not passive even with a dead source.
example : ¬Passive (affine (0 : Rat) (-2)) := by
  intro passive
  have resistive := (affine_passive_iff.mp passive).2
  norm_num at resistive

end Tests.Electronics
