import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Synthesis.Domains.Electronics.Network

namespace Synthesis.Domains.Electronics.Nodal
set_option autoImplicit false

/-! # Nodal analysis of resistive networks

Node potentials are the unknowns of the standard analysis method. The nodal operator
sends a potential assignment to the currents it injects at the nodes; solving a
resistive circuit means inverting it against a given injection.

The operator is linear, which gives superposition, and it annihilates constant
potentials, which is the freedom to choose a reference node. The main result is that
this is the *only* freedom: with strictly positive branch conductances, two potentials
producing the same injections have identical branch voltages and currents, so the
electrical solution is unique even though the potentials are not.

Positive conductances are a hypothesis, not a consequence: a network containing an
active element is outside this theorem. -/

open Network

variable {K Branch Node : Type*}

section Field
variable [Field K] [Fintype Branch] [DecidableEq Node]

/-- Currents forced by Ohm's law from a potential assignment. -/
def current (t : Topology Branch Node) (conductance : Branch → K) (potential : Node → K)
    (b : Branch) : K := conductance b * branchVoltage t potential b

/-- The nodal operator: the current injected at each node by a potential assignment. -/
def operator (t : Topology Branch Node) (conductance : Branch → K) (potential : Node → K)
    (n : Node) : K := injection t (current t conductance potential) n

/-- A potential assignment solves the network for a given injection pattern. -/
def Solves (t : Topology Branch Node) (conductance : Branch → K) (potential : Node → K)
    (injected : Node → K) : Prop := ∀ n, operator t conductance potential n = injected n

omit [Fintype Branch] [DecidableEq Node] in
theorem current_add (t : Topology Branch Node) (conductance : Branch → K) (u w : Node → K)
    (b : Branch) :
    current t conductance (fun n => u n + w n) b =
      current t conductance u b + current t conductance w b := by
  simp only [current, branchVoltage]
  ring

omit [Fintype Branch] [DecidableEq Node] in
theorem current_smul (t : Topology Branch Node) (conductance : Branch → K) (a : K)
    (u : Node → K) (b : Branch) :
    current t conductance (fun n => a * u n) b = a * current t conductance u b := by
  simp only [current, branchVoltage]
  ring

/-- The operator is additive, which is superposition of independent excitations. -/
theorem operator_add (t : Topology Branch Node) (conductance : Branch → K) (u w : Node → K)
    (n : Node) :
    operator t conductance (fun m => u m + w m) n =
      operator t conductance u n + operator t conductance w n := by
  simp only [operator, injection, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [current_add]
  ring

theorem operator_smul (t : Topology Branch Node) (conductance : Branch → K) (a : K)
    (u : Node → K) (n : Node) :
    operator t conductance (fun m => a * u m) n = a * operator t conductance u n := by
  simp only [operator, injection, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [current_smul]
  ring

/-- A uniform potential drives no current: the choice of reference node is free. -/
theorem operator_constant (t : Topology Branch Node) (conductance : Branch → K) (c : K)
    (n : Node) : operator t conductance (fun _ => c) n = 0 := by
  simp [operator, injection, current, branchVoltage]

/-- Shifting every potential by a constant leaves the injections unchanged. -/
theorem operator_shift (t : Topology Branch Node) (conductance : Branch → K) (u : Node → K)
    (c : K) (n : Node) :
    operator t conductance (fun m => u m + c) n = operator t conductance u n := by
  rw [operator_add t conductance u (fun _ => c) n, operator_constant, add_zero]

/-- **Superposition**: solutions for separate injection patterns add to a solution for
the combined pattern. -/
theorem superposition (t : Topology Branch Node) (conductance : Branch → K) {u w : Node → K}
    {left right : Node → K} (solvesLeft : Solves t conductance u left)
    (solvesRight : Solves t conductance w right) :
    Solves t conductance (fun n => u n + w n) (fun n => left n + right n) := by
  intro n
  rw [operator_add, solvesLeft n, solvesRight n]

/-- The branch currents of a solution with no injection satisfy Kirchhoff's current law. -/
theorem kcl_of_source_free (t : Topology Branch Node) (conductance : Branch → K)
    {u : Node → K} (sourceFree : Solves t conductance u (fun _ => 0)) :
    KCL t (current t conductance u) := fun n => sourceFree n

section Power
variable [Fintype Node]

/-- Power identity: the injected power equals the sum of branch powers. It follows from
Tellegen's theorem applied to the Ohmic currents. -/
theorem power_identity (t : Topology Branch Node) (conductance : Branch → K) (u : Node → K) :
    ∑ n, u n * operator t conductance u n =
      ∑ b, conductance b * branchVoltage t u b ^ 2 := by
  simp only [operator]
  rw [← tellegen_general t u (current t conductance u)]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [current]
  ring

end Power
end Field

section Ordered
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [Fintype Branch] [Fintype Node] [DecidableEq Node]

/-- A source-free passive network stores no circulating solution: every branch voltage
vanishes when all conductances are strictly positive. -/
theorem branch_voltage_zero (t : Topology Branch Node) {conductance : Branch → K}
    (passive : ∀ b, 0 < conductance b) {u : Node → K}
    (sourceFree : Solves t conductance u (fun _ => 0)) (b : Branch) :
    branchVoltage t u b = 0 := by
  have dissipation : ∑ c, conductance c * branchVoltage t u c ^ 2 = 0 := by
    rw [← power_identity]
    exact Finset.sum_eq_zero fun n _ => by rw [sourceFree n, mul_zero]
  have nonneg : ∀ c ∈ Finset.univ, 0 ≤ conductance c * branchVoltage t u c ^ 2 :=
    fun c _ => mul_nonneg (le_of_lt (passive c)) (sq_nonneg _)
  have vanishes := (Finset.sum_eq_zero_iff_of_nonneg nonneg).mp dissipation b (Finset.mem_univ b)
  have square : branchVoltage t u b ^ 2 = 0 := by
    rcases mul_eq_zero.mp vanishes with zero | zero
    · exact absurd zero (ne_of_gt (passive b))
    · exact zero
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp square

/-- **Uniqueness of the resistive solution.** Two potential assignments with the same
node injections produce the same branch voltages, hence the same branch currents. The
potentials themselves may differ by the reference offset, which is not observable. -/
theorem branch_voltage_unique (t : Topology Branch Node) {conductance : Branch → K}
    (passive : ∀ b, 0 < conductance b) {u w injected : Node → K}
    (solvesU : Solves t conductance u injected) (solvesW : Solves t conductance w injected)
    (b : Branch) : branchVoltage t u b = branchVoltage t w b := by
  have difference : Solves t conductance (fun n => u n + (-1) * w n) (fun _ => 0) := by
    intro n
    rw [operator_add, operator_smul, solvesU n, solvesW n]
    ring
  have vanishes := branch_voltage_zero t passive difference b
  simp only [branchVoltage] at vanishes ⊢
  linarith

theorem current_unique (t : Topology Branch Node) {conductance : Branch → K}
    (passive : ∀ b, 0 < conductance b) {u w injected : Node → K}
    (solvesU : Solves t conductance u injected) (solvesW : Solves t conductance w injected)
    (b : Branch) : current t conductance u b = current t conductance w b := by
  simp only [current]
  rw [branch_voltage_unique t passive solvesU solvesW b]

/-- The dissipated power of a solution is determined by its injections, and is therefore
also independent of the reference potential. -/
theorem dissipation_unique (t : Topology Branch Node) {conductance : Branch → K}
    (passive : ∀ b, 0 < conductance b) {u w injected : Node → K}
    (solvesU : Solves t conductance u injected) (solvesW : Solves t conductance w injected) :
    ∑ b, conductance b * branchVoltage t u b ^ 2 =
      ∑ b, conductance b * branchVoltage t w b ^ 2 :=
  Finset.sum_congr rfl fun b _ => by
    rw [branch_voltage_unique t passive solvesU solvesW b]

end Ordered
end Synthesis.Domains.Electronics.Nodal
