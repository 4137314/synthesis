import Synthesis.Physics.Rational

namespace Synthesis.Domains.Quantum
set_option autoImplicit false

/-- Exact complex rational amplitudes, a subfield of complex numbers.
This representation does not include arbitrary phases or 1 / sqrt(2). -/
structure Amplitude where
  re : Rat
  im : Rat
  deriving Repr, DecidableEq

def Amplitude.add (a b : Amplitude) : Amplitude := ⟨a.re + b.re, a.im + b.im⟩
def Amplitude.mul (a b : Amplitude) : Amplitude :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def Amplitude.neg (a : Amplitude) : Amplitude := ⟨-a.re, -a.im⟩
def Amplitude.timesI (a : Amplitude) : Amplitude := ⟨-a.im, a.re⟩
def Amplitude.normSquared (a : Amplitude) : Rat := a.re * a.re + a.im * a.im

theorem Amplitude.norm_nonnegative (a : Amplitude) : 0 ≤ a.normSquared :=
  Rat.add_nonneg (Physics.square_nonnegative a.re) (Physics.square_nonnegative a.im)

structure Qubit where
  zero : Amplitude
  one : Amplitude
  deriving Repr, DecidableEq

def Qubit.add (a b : Qubit) : Qubit := ⟨a.zero.add b.zero, a.one.add b.one⟩
def Qubit.scale (c : Amplitude) (a : Qubit) : Qubit := ⟨c.mul a.zero, c.mul a.one⟩
def Qubit.normSquared (q : Qubit) : Rat := q.zero.normSquared + q.one.normSquared

def Qubit.Normalized (q : Qubit) : Prop := q.normSquared = 1

/-- A reversible complex-linear norm-preserving map in the exact rational model. -/
structure Gate where
  run : Qubit → Qubit
  inverse : Qubit → Qubit
  left_inverse : ∀ q, inverse (run q) = q
  right_inverse : ∀ q, run (inverse q) = q
  additive : ∀ a b, run (a.add b) = (run a).add (run b)
  homogeneous : ∀ c q, run (q.scale c) = (run q).scale c
  norm_preserving : ∀ q, (run q).normSquared = q.normSquared

theorem Gate.preserves_normalization (gate : Gate) (q : Qubit) (h : q.Normalized) :
    (gate.run q).Normalized := (gate.norm_preserving q).trans h

def Gate.andThen (first second : Gate) : Gate where
  run q := second.run (first.run q)
  inverse q := first.inverse (second.inverse q)
  left_inverse q := by rw [second.left_inverse, first.left_inverse]
  right_inverse q := by rw [first.right_inverse, second.right_inverse]
  additive a b := by rw [first.additive, second.additive]
  homogeneous c q := by rw [first.homogeneous, second.homogeneous]
  norm_preserving q := by rw [second.norm_preserving, first.norm_preserving]

/-- Pauli X exchanges the two basis amplitudes. -/
def x : Gate where
  run q := ⟨q.one, q.zero⟩
  inverse q := ⟨q.one, q.zero⟩
  left_inverse _ := rfl
  right_inverse _ := rfl
  additive _ _ := rfl
  homogeneous _ _ := rfl
  norm_preserving q := by simp only [Qubit.normSquared]; grind

/-- Pauli Z changes the sign of the |1> amplitude. -/
def z : Gate where
  run q := ⟨q.zero, q.one.neg⟩
  inverse q := ⟨q.zero, q.one.neg⟩
  left_inverse q := by cases q with | mk a b => cases b; simp [Amplitude.neg]
  right_inverse q := by cases q with | mk a b => cases b; simp [Amplitude.neg]
  additive a b := by
    simp only [Qubit.add, Amplitude.add, Amplitude.neg]
    congr 2 <;> grind
  homogeneous c q := by
    simp only [Qubit.scale, Amplitude.mul, Amplitude.neg]
    congr 2 <;> grind
  norm_preserving q := by
    simp only [Qubit.normSquared, Amplitude.normSquared, Amplitude.neg]
    grind

/-- Phase S multiplies the |1> amplitude by i. -/
def phase : Gate where
  run q := ⟨q.zero, q.one.timesI⟩
  inverse q := ⟨q.zero, q.one.timesI.neg⟩
  left_inverse q := by cases q with | mk a b => cases b; simp [Amplitude.timesI, Amplitude.neg]
  right_inverse q := by cases q with | mk a b => cases b; simp [Amplitude.timesI, Amplitude.neg]
  additive a b := by
    simp only [Qubit.add, Amplitude.add, Amplitude.timesI]
    congr 2 <;> grind
  homogeneous c q := by
    simp only [Qubit.scale, Amplitude.mul, Amplitude.timesI]
    congr 2 <;> grind
  norm_preserving q := by
    simp only [Qubit.normSquared, Amplitude.normSquared, Amplitude.timesI]
    grind

theorem x_involution (q : Qubit) : x.run (x.run q) = q := rfl

theorem z_involution (q : Qubit) : z.run (z.run q) = q := z.left_inverse q

theorem phase_squared (q : Qubit) : phase.run (phase.run q) = z.run q := by
  simp [phase, z, Amplitude.timesI, Amplitude.neg]

end Synthesis.Domains.Quantum
