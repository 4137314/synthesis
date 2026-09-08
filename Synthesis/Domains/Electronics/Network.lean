import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace Synthesis.Domains.Electronics.Network
set_option autoImplicit false

/-! # Kirchhoff's laws and Tellegen's theorem

A lumped interconnection is a finite directed multigraph: branches carry currents and
nodes carry potentials. Kirchhoff's current law is a linear constraint on branch
currents, and Kirchhoff's voltage law holds by construction whenever branch voltages
are potential differences.

Tellegen's theorem is proved here in its strong form: the currents and the potentials
may come from *different* operating points, and even from different constitutive laws,
as long as they share the topology. Conservation of power is the special case in which
both come from the same solution.

The model is quasi-static and lumped. Radiation, mutual coupling between branches and
distributed effects are outside it, and no theorem below asserts their absence in a
physical circuit. -/

variable {K : Type*} {Branch Node : Type*}

/-- A lumped topology orients every branch from a source node to a target node.
Self-loops are permitted and carry no potential difference. -/
structure Topology (Branch Node : Type*) where
  source : Branch → Node
  target : Branch → Node

section Ring
variable [CommRing K] [Fintype Branch] [Fintype Node] [DecidableEq Node]

/-- Reduced incidence coefficient of a branch at a node: `+1` at its source, `-1` at
its target, `0` elsewhere, and `0` at both ends of a self-loop. -/
def incidence (t : Topology Branch Node) (b : Branch) (n : Node) : K :=
  (if t.source b = n then 1 else 0) - (if t.target b = n then 1 else 0)

/-- Branch voltage induced by a node potential, in the passive sign convention. -/
def branchVoltage (t : Topology Branch Node) (u : Node → K) (b : Branch) : K :=
  u (t.source b) - u (t.target b)

/-- Net current leaving a node, the left-hand side of Kirchhoff's current law. -/
def injection (t : Topology Branch Node) (i : Branch → K) (n : Node) : K :=
  ∑ b, incidence t b n * i b

/-- Kirchhoff's current law: no charge accumulates at any node. -/
def KCL (t : Topology Branch Node) (i : Branch → K) : Prop := ∀ n, injection t i n = 0

omit [Fintype Branch] in
/-- Every branch has one source and one target, so its incidence column sums to zero.
This is the graph-level statement that a branch neither creates nor destroys current. -/
theorem incidence_column_sum (t : Topology Branch Node) (b : Branch) :
    ∑ n, incidence t b n = (0 : K) := by
  simp [incidence, Finset.sum_sub_distrib]

omit [Fintype Branch] in
/-- Node potentials reproduce branch voltages through the incidence coefficients. -/
theorem incidence_potential (t : Topology Branch Node) (u : Node → K) (b : Branch) :
    ∑ n, incidence t b n * u n = branchVoltage t u b := by
  simp [incidence, branchVoltage, sub_mul, Finset.sum_sub_distrib]

omit [Fintype Branch] [Fintype Node] [DecidableEq Node] in
/-- A self-loop carries no voltage: Kirchhoff's voltage law degenerates correctly. -/
theorem self_loop_voltage (t : Topology Branch Node) (u : Node → K) (b : Branch)
    (loop : t.source b = t.target b) : branchVoltage t u b = 0 := by
  simp [branchVoltage, loop]

/-- Total injected current over all nodes vanishes identically, whether or not the
currents satisfy Kirchhoff's law. A network cannot be a net source of charge. -/
theorem injection_total (t : Topology Branch Node) (i : Branch → K) :
    ∑ n, injection t i n = (0 : K) := by
  simp only [injection]
  rw [Finset.sum_comm]
  calc ∑ b, ∑ n, incidence t b n * i b
      = ∑ b : Branch, (∑ n, incidence t b n) * i b := by
        exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]
    _ = 0 := by simp [incidence_column_sum]

/-- **Tellegen's theorem**, general form. For any potential assignment and any current
assignment on the same topology, the branch power sum equals the power injected at the
nodes. Neither assignment needs to satisfy a constitutive law. -/
theorem tellegen_general (t : Topology Branch Node) (u : Node → K) (i : Branch → K) :
    ∑ b, branchVoltage t u b * i b = ∑ n, u n * injection t i n := by
  calc ∑ b, branchVoltage t u b * i b
      = ∑ b : Branch, ∑ n, incidence t b n * u n * i b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← incidence_potential t u b, Finset.sum_mul]
    _ = ∑ n : Node, ∑ b, u n * (incidence t b n * i b) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ n, u n * injection t i n := by
        exact Finset.sum_congr rfl fun n _ => by rw [injection, Finset.mul_sum]

/-- **Tellegen's theorem**. Under Kirchhoff's current law the total branch power
vanishes, for voltages taken from any potential assignment whatsoever. -/
theorem tellegen (t : Topology Branch Node) (u : Node → K) (i : Branch → K)
    (kcl : KCL t i) : ∑ b, branchVoltage t u b * i b = 0 := by
  rw [tellegen_general]
  exact Finset.sum_eq_zero fun n _ => by rw [kcl n, mul_zero]

/-- Conservation of power in a source-free network: what some branches absorb, others
deliver. This is the physical reading of Tellegen's theorem. -/
theorem power_conservation (t : Topology Branch Node) (u : Node → K) (i : Branch → K)
    (kcl : KCL t i) (v : Branch → K) (ohm : ∀ b, v b = branchVoltage t u b) :
    ∑ b, v b * i b = 0 := by
  rw [show (fun b => v b * i b) = fun b => branchVoltage t u b * i b from
    funext fun b => by rw [ohm b]]
  exact tellegen t u i kcl

omit [Fintype Node] [DecidableEq Node] in
/-- Kirchhoff's voltage law: the branch voltages around any closed walk sum to zero.
The walk is given by its node sequence; the identity is a telescoping sum, so it holds
for every potential assignment. -/
theorem kvl_closed_walk (u : Node → K) (steps : ℕ) (walk : ℕ → Node)
    (closed : walk steps = walk 0) :
    ∑ k ∈ Finset.range steps, (u (walk k) - u (walk (k + 1))) = 0 := by
  rw [Finset.sum_range_sub' (fun k => u (walk k)) steps, closed, sub_self]

omit [Fintype Branch] [Fintype Node] [DecidableEq Node] in
/-- Kirchhoff's voltage law along a walk that follows oriented branches. -/
theorem kvl_branch_walk (t : Topology Branch Node) (u : Node → K) (steps : ℕ)
    (path : ℕ → Branch) (connected : ∀ k, t.target (path k) = t.source (path (k + 1)))
    (closed : t.source (path steps) = t.source (path 0)) :
    ∑ k ∈ Finset.range steps, branchVoltage t u (path k) = 0 := by
  have rewritten : ∀ k ∈ Finset.range steps, branchVoltage t u (path k) =
      u (t.source (path k)) - u (t.source (path (k + 1))) := by
    intro k _
    rw [branchVoltage, connected k]
  rw [Finset.sum_congr rfl rewritten]
  exact kvl_closed_walk u steps (fun k => t.source (path k)) closed

omit [Fintype Node] in
/-- Superposition of Kirchhoff-admissible currents: the constraint set is a subspace. -/
theorem kcl_add (t : Topology Branch Node) (i j : Branch → K)
    (hi : KCL t i) (hj : KCL t j) : KCL t (fun b => i b + j b) := by
  intro n
  have expand : injection t (fun b => i b + j b) n = injection t i n + injection t j n := by
    simp only [injection, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [expand, hi n, hj n, add_zero]

omit [Fintype Node] in
theorem kcl_smul (t : Topology Branch Node) (a : K) (i : Branch → K) (hi : KCL t i) :
    KCL t (fun b => a * i b) := by
  intro n
  have expand : injection t (fun b => a * i b) n = a * injection t i n := by
    simp only [injection, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [expand, hi n, mul_zero]

omit [Fintype Node] in
theorem kcl_zero (t : Topology Branch Node) : KCL t (fun _ => (0 : K)) := by
  intro n
  simp [injection]

end Ring

section Ordered
variable [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
variable [Fintype Branch] [Fintype Node] [DecidableEq Node]

/-- A resistive solution: branch conductances, node potentials and the branch currents
they force through Ohm's law. Sources enter as node injections. -/
structure ResistiveSolution {Branch Node : Type*} (K : Type*) [CommRing K] [PartialOrder K]
    (t : Topology Branch Node) where
  conductance : Branch → K
  potential : Node → K
  passive : ∀ b, 0 ≤ conductance b

namespace ResistiveSolution
variable {t : Topology Branch Node}

/-- Branch voltage of the solution. -/
def voltage (s : ResistiveSolution K t) (b : Branch) : K := branchVoltage t s.potential b

/-- Branch current forced by Ohm's law. -/
def current (s : ResistiveSolution K t) (b : Branch) : K := s.conductance b * s.voltage b

/-- Total dissipated power of the solution. -/
def dissipation (s : ResistiveSolution K t) : K := ∑ b, s.conductance b * (s.voltage b * s.voltage b)

omit [IsStrictOrderedRing K] [Fintype Branch] [Fintype Node] [DecidableEq Node] in
theorem branch_power (s : ResistiveSolution K t) (b : Branch) :
    s.voltage b * s.current b = s.conductance b * (s.voltage b * s.voltage b) := by
  simp only [current]
  ring

omit [Fintype Node] [DecidableEq Node] in
/-- A resistive network dissipates nonnegative power at every operating point. -/
theorem dissipation_nonnegative (s : ResistiveSolution K t) : 0 ≤ s.dissipation :=
  Finset.sum_nonneg fun b _ => mul_nonneg (s.passive b) (mul_self_nonneg _)

omit [IsStrictOrderedRing K] in
/-- The dissipated power equals the power injected at the nodes: a resistive network
consumes exactly what its sources deliver. -/
theorem dissipation_eq_injection (s : ResistiveSolution K t) :
    s.dissipation = ∑ n, s.potential n * injection t s.current n := by
  rw [← tellegen_general t s.potential s.current]
  exact Finset.sum_congr rfl fun b _ => (branch_power s b).symm

omit [IsStrictOrderedRing K] in
/-- A resistive network with no external injection dissipates no power: its only
Kirchhoff-admissible operating point is loss-free. -/
theorem dissipation_zero_of_kcl (s : ResistiveSolution K t) (kcl : KCL t s.current) :
    s.dissipation = 0 := by
  rw [dissipation_eq_injection]
  exact Finset.sum_eq_zero fun n _ => by rw [kcl n, mul_zero]

/-- With no external injection every branch is individually loss-free, so a passive
source-free network has no internally circulating dissipation. -/
theorem branch_dissipation_zero (s : ResistiveSolution K t) (kcl : KCL t s.current)
    (b : Branch) : s.conductance b * (s.voltage b * s.voltage b) = 0 := by
  have total := dissipation_zero_of_kcl s kcl
  have nonneg : ∀ c ∈ Finset.univ, 0 ≤ s.conductance c * (s.voltage c * s.voltage c) :=
    fun c _ => mul_nonneg (s.passive c) (mul_self_nonneg _)
  exact (Finset.sum_eq_zero_iff_of_nonneg nonneg).mp total b (Finset.mem_univ b)

end ResistiveSolution
end Ordered
end Synthesis.Domains.Electronics.Network
