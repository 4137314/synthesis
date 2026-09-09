import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Synthesis.Domains.Electronics.Ode

namespace Synthesis.Domains.Electronics.SecondOrder
set_option autoImplicit false

/-! # Second-order relaxation

A circuit with two independent storage elements and one dissipative path obeys
`x'' + a x' + b x = 0`. This module is the mathematics of that equation, parameterized
by the two coefficients rather than by the damping ratio and the natural frequency, so
that the constructors of `Synthesis.Domains.Electronics.Rlc` are division-free and no
square root appears in the circuit derivation. The engineering vocabulary is recovered
as derived quantities: `naturalFrequency` is `sqrt b`, `dampingRatio` is `a / (2 sqrt b)`.

The behaviour splits on the sign of the discriminant `a² - 4 b`, and each regime is
treated separately and exactly:

* **overdamped** (`0 < discriminant`): two distinct real characteristic roots. Each mode
  solves the equation, and `overdamped_decomposition` proves the converse, that *every*
  solution is a combination of the two modes. Uniqueness follows.
* **critically damped** (`discriminant = 0`): one repeated root; the second mode carries
  the factor `t`.
* **underdamped** (`discriminant < 0`): no real root at all, proved in
  `no_real_root`, so the response necessarily oscillates; the decaying sinusoid family
  is verified in `oscillatory_solves`.

Nonnegative dissipation and positive stiffness are hypotheses of the structure, not
consequences: an active circuit does not satisfy them, and every stability statement
below rests on them. Nothing here bounds the modelling error of a lumped description,
and no theorem asserts that a physical circuit is linear or time invariant. -/

/-- A damped second-order relaxation `x'' + a x' + b x = 0` with nonnegative dissipation
and strictly positive stiffness. Zero stiffness would degenerate to a first-order
equation, which has its own model in `Synthesis.Domains.Electronics.Transient`. -/
structure Damped where
  dissipation : ℝ
  stiffness : ℝ
  dissipationNonneg : 0 ≤ dissipation
  stiffnessPositive : 0 < stiffness

namespace Damped

/-- The characteristic polynomial whose roots are the exponential modes. -/
def characteristic (d : Damped) (s : ℝ) : ℝ := s ^ 2 + d.dissipation * s + d.stiffness

/-- Discriminant of the characteristic polynomial; its sign selects the regime. -/
def discriminant (d : Damped) : ℝ := d.dissipation ^ 2 - 4 * d.stiffness

/-- Undamped natural angular frequency `ω₀ = sqrt b`. -/
noncomputable def naturalFrequency (d : Damped) : ℝ := Real.sqrt d.stiffness

/-- Damping ratio `ζ = a / (2 ω₀)`, the dimensionless form of the dissipation. -/
noncomputable def dampingRatio (d : Damped) : ℝ := d.dissipation / (2 * Real.sqrt d.stiffness)

/-- Exponential decay rate of the envelope, `α = a / 2`. -/
noncomputable def decayRate (d : Damped) : ℝ := d.dissipation / 2

theorem naturalFrequency_positive (d : Damped) : 0 < d.naturalFrequency :=
  Real.sqrt_pos.mpr d.stiffnessPositive

theorem naturalFrequency_sq (d : Damped) : d.naturalFrequency ^ 2 = d.stiffness :=
  Real.sq_sqrt (le_of_lt d.stiffnessPositive)

theorem dampingRatio_nonneg (d : Damped) : 0 ≤ d.dampingRatio :=
  div_nonneg d.dissipationNonneg (by positivity)

/-- The two parameterizations agree: `a = 2 ζ ω₀`. -/
theorem dissipation_eq (d : Damped) :
    d.dissipation = 2 * d.dampingRatio * d.naturalFrequency := by
  have positive := d.naturalFrequency_positive
  simp only [dampingRatio, naturalFrequency] at *
  field_simp

/-- The damping ratio recovers the dissipation: `4 b ζ² = a²`. -/
theorem dampingRatio_sq (d : Damped) :
    4 * d.stiffness * d.dampingRatio ^ 2 = d.dissipation ^ 2 := by
  have square : Real.sqrt d.stiffness ^ 2 = d.stiffness :=
    Real.sq_sqrt (le_of_lt d.stiffnessPositive)
  have nonzero : d.stiffness ≠ 0 := ne_of_gt d.stiffnessPositive
  simp only [dampingRatio, div_pow, mul_pow, square]
  field_simp
  ring

/-- The discriminant in dimensionless form: its sign is the sign of `ζ² - 1`. -/
theorem discriminant_eq (d : Damped) :
    d.discriminant = 4 * d.stiffness * (d.dampingRatio ^ 2 - 1) := by
  have square := d.dampingRatio_sq
  simp only [discriminant]
  linear_combination -square

/-- Completing the square, the identity behind every regime statement. -/
theorem characteristic_completed (d : Damped) (s : ℝ) :
    4 * d.characteristic s = (2 * s + d.dissipation) ^ 2 - d.discriminant := by
  simp only [characteristic, discriminant]
  ring

/-! ## Solutions -/

/-- A trajectory solves the relaxation when its first and second derivatives exist and
satisfy the equation pointwise. The rate and the acceleration are supplied as functions
so that differentiability is stated once for each. -/
def Solves (d : Damped) (x rate acceleration : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt x (rate t) t) ∧ (∀ t, HasDerivAt rate (acceleration t) t) ∧
    ∀ t, acceleration t + d.dissipation * rate t + d.stiffness * x t = 0

/-- Solutions add: the equation is linear. -/
theorem solves_add {d : Damped} {x xr xa y yr ya : ℝ → ℝ}
    (first : d.Solves x xr xa) (second : d.Solves y yr ya) :
    d.Solves (fun t => x t + y t) (fun t => xr t + yr t) (fun t => xa t + ya t) := by
  refine ⟨fun t => (first.1 t).add (second.1 t), fun t => (first.2.1 t).add (second.2.1 t),
    fun t => ?_⟩
  show xa t + ya t + d.dissipation * (xr t + yr t) + d.stiffness * (x t + y t) = 0
  linear_combination first.2.2 t + second.2.2 t

theorem solves_smul {d : Damped} {x rate acceleration : ℝ → ℝ}
    (solution : d.Solves x rate acceleration) (c : ℝ) :
    d.Solves (fun t => c * x t) (fun t => c * rate t) (fun t => c * acceleration t) := by
  refine ⟨fun t => (solution.1 t).const_mul c, fun t => (solution.2.1 t).const_mul c, fun t => ?_⟩
  show c * acceleration t + d.dissipation * (c * rate t) + d.stiffness * (c * x t) = 0
  linear_combination c * solution.2.2 t

end Damped

/-! ## Exponential modes -/

/-- A single exponential mode `c e^{s t}`. -/
noncomputable def mode (s c : ℝ) : ℝ → ℝ := fun t => c * Real.exp (s * t)

theorem mode_zero (s c : ℝ) : mode s c 0 = c := by simp [mode]

theorem hasDerivAt_mode (s c t : ℝ) : HasDerivAt (mode s c) (mode s (s * c) t) t := by
  have derivative := Ode.hasDerivAt_exponential s c t
  have value : s * (c * Real.exp (s * t)) = mode s (s * c) t := by
    simp only [mode]
    ring
  rwa [value] at derivative

/-- **Every characteristic root gives a solution.** The mode is a solution of the
relaxation exactly because its exponent annihilates the characteristic polynomial. -/
theorem mode_solves (d : Damped) {s : ℝ} (root : d.characteristic s = 0) (c : ℝ) :
    d.Solves (mode s c) (mode s (s * c)) (mode s (s * (s * c))) := by
  refine ⟨fun t => hasDerivAt_mode s c t, fun t => hasDerivAt_mode s (s * c) t, fun t => ?_⟩
  simp only [mode, Damped.characteristic] at root ⊢
  linear_combination c * Real.exp (s * t) * root

/-! ## The overdamped regime -/

namespace Damped

/-- The characteristic root of larger value, which dominates the long-time response. -/
noncomputable def slowRoot (d : Damped) : ℝ := (-d.dissipation + Real.sqrt d.discriminant) / 2

/-- The characteristic root of smaller value, the fast-decaying mode. -/
noncomputable def fastRoot (d : Damped) : ℝ := (-d.dissipation - Real.sqrt d.discriminant) / 2

theorem sqrt_discriminant_sq {d : Damped} (real : 0 ≤ d.discriminant) :
    Real.sqrt d.discriminant ^ 2 = d.dissipation ^ 2 - 4 * d.stiffness := by
  rw [Real.sq_sqrt real]
  rfl

theorem characteristic_slowRoot {d : Damped} (real : 0 ≤ d.discriminant) :
    d.characteristic d.slowRoot = 0 := by
  have square := sqrt_discriminant_sq real
  simp only [characteristic, slowRoot]
  linear_combination square / 4

theorem characteristic_fastRoot {d : Damped} (real : 0 ≤ d.discriminant) :
    d.characteristic d.fastRoot = 0 := by
  have square := sqrt_discriminant_sq real
  simp only [characteristic, fastRoot]
  linear_combination square / 4

/-- The roots reproduce the coefficients, which is the factorization of the
characteristic polynomial. -/
theorem root_sum (d : Damped) : d.slowRoot + d.fastRoot = -d.dissipation := by
  simp only [slowRoot, fastRoot]
  ring

theorem root_product {d : Damped} (real : 0 ≤ d.discriminant) :
    d.slowRoot * d.fastRoot = d.stiffness := by
  have square := sqrt_discriminant_sq real
  simp only [slowRoot, fastRoot]
  linear_combination -square / 4

/-- **Stability of the real regime**: both characteristic roots are strictly negative, so
every exponential mode decays. Positive stiffness is what excludes a root at the origin
and nonnegative dissipation is what excludes a growing mode. -/
theorem slowRoot_negative {d : Damped} (real : 0 ≤ d.discriminant) : d.slowRoot < 0 := by
  have stiffness := d.stiffnessPositive
  have nonneg := d.dissipationNonneg
  have square := sqrt_discriminant_sq real
  have root : 0 ≤ Real.sqrt d.discriminant := Real.sqrt_nonneg _
  have expand : d.discriminant = d.dissipation ^ 2 - 4 * d.stiffness := rfl
  have dissipative : 0 < d.dissipation := by
    rcases eq_or_lt_of_le nonneg with degenerate | positive
    · exfalso
      rw [expand, ← degenerate] at real
      nlinarith [d.stiffnessPositive]
    · exact positive
  have strict : Real.sqrt d.discriminant < d.dissipation := by
    nlinarith [square, root, dissipative, stiffness]
  simp only [slowRoot]
  linarith

theorem fastRoot_negative {d : Damped} (real : 0 ≤ d.discriminant) : d.fastRoot < 0 := by
  have slow := slowRoot_negative real
  have root : 0 ≤ Real.sqrt d.discriminant := Real.sqrt_nonneg _
  simp only [slowRoot] at slow
  simp only [fastRoot]
  linarith

/-- Strictly positive discriminant separates the two roots, which is what makes the two
modes independent. -/
theorem roots_distinct {d : Damped} (overdamped : 0 < d.discriminant) :
    d.fastRoot < d.slowRoot := by
  have root : 0 < Real.sqrt d.discriminant := Real.sqrt_pos.mpr overdamped
  simp only [slowRoot, fastRoot]
  linarith

end Damped

/-- **Completeness of the overdamped modes.** Every solution of an overdamped relaxation
is a combination of its two exponential modes, so the mode family is not merely a source
of solutions but a description of all of them. Uniqueness for given initial conditions
is the immediate consequence. -/
theorem overdamped_decomposition (d : Damped) (overdamped : 0 < d.discriminant)
    {x rate acceleration : ℝ → ℝ} (solution : d.Solves x rate acceleration) :
    ∃ a b : ℝ, x = fun t => a * Real.exp (d.fastRoot * t) + b * Real.exp (d.slowRoot * t) := by
  have real : 0 ≤ d.discriminant := le_of_lt overdamped
  have separated : d.fastRoot < d.slowRoot := Damped.roots_distinct overdamped
  have gap : d.slowRoot - d.fastRoot ≠ 0 := by linarith
  have sum := Damped.root_sum d
  have product := Damped.root_product real
  -- The first factor of the characteristic polynomial reduces the order.
  have residual : Ode.Linear d.slowRoot (fun t => rate t - d.fastRoot * x t)
      (fun t => acceleration t - d.fastRoot * rate t) := by
    refine ⟨fun t => (solution.2.1 t).sub ((solution.1 t).const_mul d.fastRoot), fun t => ?_⟩
    show acceleration t - d.fastRoot * rate t = d.slowRoot * (rate t - d.fastRoot * x t)
    linear_combination solution.2.2 t - rate t * sum + x t * product
  have factored : ∀ t, rate t - d.fastRoot * x t =
      (rate 0 - d.fastRoot * x 0) * Real.exp (d.slowRoot * t) :=
    fun t => Ode.linear_unique residual t
  -- Subtracting the slow mode leaves a solution of the remaining first-order factor.
  obtain ⟨coefficient, scaled⟩ :
      ∃ c : ℝ, c * (d.slowRoot - d.fastRoot) = rate 0 - d.fastRoot * x 0 :=
    ⟨(rate 0 - d.fastRoot * x 0) / (d.slowRoot - d.fastRoot), by field_simp⟩
  have remainder : Ode.Linear d.fastRoot
      (fun t => x t - coefficient * Real.exp (d.slowRoot * t))
      (fun t => rate t - d.slowRoot * (coefficient * Real.exp (d.slowRoot * t))) := by
    refine ⟨fun t => (solution.1 t).sub (Ode.hasDerivAt_exponential d.slowRoot coefficient t),
      fun t => ?_⟩
    show rate t - d.slowRoot * (coefficient * Real.exp (d.slowRoot * t)) =
      d.fastRoot * (x t - coefficient * Real.exp (d.slowRoot * t))
    linear_combination factored t - Real.exp (d.slowRoot * t) * scaled
  refine ⟨x 0 - coefficient, coefficient, funext fun t => ?_⟩
  have closed : x t - coefficient * Real.exp (d.slowRoot * t) =
      (x 0 - coefficient * Real.exp (d.slowRoot * 0)) * Real.exp (d.fastRoot * t) :=
    Ode.linear_unique remainder t
  rw [mul_zero, Real.exp_zero, mul_one] at closed
  linear_combination closed

/-! ## The critically damped regime -/

/-- The repeated characteristic root of a critically damped relaxation. -/
noncomputable def Damped.doubleRoot (d : Damped) : ℝ := -d.dissipation / 2

theorem Damped.characteristic_doubleRoot {d : Damped} (critical : d.discriminant = 0) :
    d.characteristic d.doubleRoot = 0 := by
  simp only [discriminant] at critical
  simp only [characteristic, doubleRoot]
  linear_combination -critical / 4

/-- The second mode of the critically damped regime, carrying the linear factor. -/
noncomputable def criticalMode (s a b : ℝ) : ℝ → ℝ := fun t => (a + b * t) * Real.exp (s * t)

theorem criticalMode_zero (s a b : ℝ) : criticalMode s a b 0 = a := by simp [criticalMode]

theorem hasDerivAt_criticalMode (s a b t : ℝ) :
    HasDerivAt (criticalMode s a b) (criticalMode s (b + s * a) (s * b) t) t := by
  have linear : HasDerivAt (fun u : ℝ => a + b * u) b t := by
    have scaled : HasDerivAt (fun u : ℝ => b * u) b t := by
      simpa using (hasDerivAt_id t).const_mul b
    have sum := (hasDerivAt_const t a).add scaled
    rw [zero_add] at sum
    exact sum
  have inner : HasDerivAt (fun u : ℝ => s * u) s t := by
    simpa using (hasDerivAt_id t).const_mul s
  have product : HasDerivAt (criticalMode s a b)
      (b * Real.exp (s * t) + (a + b * t) * (Real.exp (s * t) * s)) t := linear.mul inner.exp
  have value : b * Real.exp (s * t) + (a + b * t) * (Real.exp (s * t) * s) =
      criticalMode s (b + s * a) (s * b) t := by
    simp only [criticalMode]
    ring
  rwa [value] at product

/-- **The critically damped family solves the relaxation.** At the repeated root the two
independent solutions are `e^{s t}` and `t e^{s t}`, and both are covered here. -/
theorem critical_solves (d : Damped) (critical : d.discriminant = 0) (a b : ℝ) :
    d.Solves (criticalMode d.doubleRoot a b)
      (criticalMode d.doubleRoot (b + d.doubleRoot * a) (d.doubleRoot * b))
      (criticalMode d.doubleRoot
        (d.doubleRoot * b + d.doubleRoot * (b + d.doubleRoot * a))
        (d.doubleRoot * (d.doubleRoot * b))) := by
  refine ⟨fun t => hasDerivAt_criticalMode _ a b t,
    fun t => hasDerivAt_criticalMode _ (b + d.doubleRoot * a) (d.doubleRoot * b) t, fun t => ?_⟩
  have stiffness : d.stiffness = d.doubleRoot ^ 2 := by
    simp only [Damped.discriminant] at critical
    simp only [Damped.doubleRoot]
    linear_combination -critical / 4
  have dissipation : d.dissipation = -2 * d.doubleRoot := by
    simp only [Damped.doubleRoot]
    ring
  simp only [criticalMode, stiffness, dissipation]
  ring

/-! ## The underdamped regime -/

/-- **No exponential mode exists below critical damping.** A negative discriminant means
the characteristic polynomial is strictly positive everywhere, so the response cannot be
a sum of real exponentials: it necessarily oscillates. -/
theorem no_real_root (d : Damped) (underdamped : d.discriminant < 0) (s : ℝ) :
    0 < d.characteristic s := by
  have completed := d.characteristic_completed s
  have square : 0 ≤ (2 * s + d.dissipation) ^ 2 := sq_nonneg _
  linarith

/-- Damped angular frequency `ω_d = sqrt (4 b - a²) / 2` of an underdamped relaxation. -/
noncomputable def Damped.dampedFrequency (d : Damped) : ℝ := Real.sqrt (-d.discriminant) / 2

theorem Damped.dampedFrequency_positive {d : Damped} (underdamped : d.discriminant < 0) :
    0 < d.dampedFrequency :=
  div_pos (Real.sqrt_pos.mpr (by linarith)) (by norm_num)

/-- The defining relation of the two envelope parameters: `α² + ω_d² = b`. -/
theorem Damped.dampedFrequency_sq {d : Damped} (underdamped : d.discriminant ≤ 0) :
    d.decayRate ^ 2 + d.dampedFrequency ^ 2 = d.stiffness := by
  have square : Real.sqrt (-d.discriminant) ^ 2 = -d.discriminant :=
    Real.sq_sqrt (by linarith)
  simp only [Damped.discriminant] at square
  simp only [Damped.decayRate, Damped.dampedFrequency, Damped.discriminant]
  linear_combination square / 4

/-- A decaying sinusoid `e^{-α t} (a cos ω t + b sin ω t)`. -/
noncomputable def oscillatoryMode (decay frequency a b : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (-decay * t) * (a * Real.cos (frequency * t) + b * Real.sin (frequency * t))

theorem oscillatoryMode_zero (decay frequency a b : ℝ) :
    oscillatoryMode decay frequency a b 0 = a := by
  simp [oscillatoryMode]

theorem hasDerivAt_oscillatoryMode (decay frequency a b t : ℝ) :
    HasDerivAt (oscillatoryMode decay frequency a b)
      (oscillatoryMode decay frequency (-decay * a + frequency * b)
        (-decay * b - frequency * a) t) t := by
  have envelope : HasDerivAt (fun u : ℝ => Real.exp (-decay * u))
      (Real.exp (-decay * t) * -decay) t := by
    have inner : HasDerivAt (fun u : ℝ => -decay * u) (-decay) t := by
      simpa using (hasDerivAt_id t).const_mul (-decay)
    exact inner.exp
  have angle : HasDerivAt (fun u : ℝ => frequency * u) frequency t := by
    simpa using (hasDerivAt_id t).const_mul frequency
  have cosine : HasDerivAt (fun u : ℝ => Real.cos (frequency * u))
      (-Real.sin (frequency * t) * frequency) t := angle.cos
  have sine : HasDerivAt (fun u : ℝ => Real.sin (frequency * u))
      (Real.cos (frequency * t) * frequency) t := angle.sin
  have wave : HasDerivAt
      (fun u : ℝ => a * Real.cos (frequency * u) + b * Real.sin (frequency * u))
      (a * (-Real.sin (frequency * t) * frequency) +
        b * (Real.cos (frequency * t) * frequency)) t :=
    (cosine.const_mul a).add (sine.const_mul b)
  have product : HasDerivAt (oscillatoryMode decay frequency a b)
      (Real.exp (-decay * t) * -decay *
          (a * Real.cos (frequency * t) + b * Real.sin (frequency * t)) +
        Real.exp (-decay * t) *
          (a * (-Real.sin (frequency * t) * frequency) +
            b * (Real.cos (frequency * t) * frequency))) t := envelope.mul wave
  have value : Real.exp (-decay * t) * -decay *
        (a * Real.cos (frequency * t) + b * Real.sin (frequency * t)) +
      Real.exp (-decay * t) *
        (a * (-Real.sin (frequency * t) * frequency) +
          b * (Real.cos (frequency * t) * frequency)) =
      oscillatoryMode decay frequency (-decay * a + frequency * b)
        (-decay * b - frequency * a) t := by
    simp only [oscillatoryMode]
    ring
  rwa [value] at product

/-- **The underdamped family solves the relaxation.** The decaying sinusoid with the
envelope decay `α = a / 2` and the damped frequency `ω_d` satisfies the equation for
every pair of amplitudes, which is the ringing response of a lightly damped circuit. -/
theorem oscillatory_solves (d : Damped) (underdamped : d.discriminant ≤ 0) (a b : ℝ) :
    d.Solves (oscillatoryMode d.decayRate d.dampedFrequency a b)
      (oscillatoryMode d.decayRate d.dampedFrequency
        (-d.decayRate * a + d.dampedFrequency * b) (-d.decayRate * b - d.dampedFrequency * a))
      (oscillatoryMode d.decayRate d.dampedFrequency
        (-d.decayRate * (-d.decayRate * a + d.dampedFrequency * b) +
          d.dampedFrequency * (-d.decayRate * b - d.dampedFrequency * a))
        (-d.decayRate * (-d.decayRate * b - d.dampedFrequency * a) -
          d.dampedFrequency * (-d.decayRate * a + d.dampedFrequency * b))) := by
  refine ⟨fun t => hasDerivAt_oscillatoryMode _ _ a b t,
    fun t => hasDerivAt_oscillatoryMode _ _ _ _ t, fun t => ?_⟩
  have envelope := Damped.dampedFrequency_sq underdamped
  have dissipation : d.dissipation = 2 * d.decayRate := by
    simp only [Damped.decayRate]
    ring
  simp only [oscillatoryMode, dissipation, ← envelope]
  ring

/-- The underdamped response is bounded by its exponential envelope, which is the
statement that ringing decays rather than persisting. -/
theorem oscillatory_envelope (decay frequency a b t : ℝ) :
    |oscillatoryMode decay frequency a b t| ≤
      Real.exp (-decay * t) * (|a| + |b|) := by
  have positive : (0 : ℝ) < Real.exp (-decay * t) := Real.exp_pos _
  have cosine : |Real.cos (frequency * t)| ≤ 1 := Real.abs_cos_le_one _
  have sine : |Real.sin (frequency * t)| ≤ 1 := Real.abs_sin_le_one _
  simp only [oscillatoryMode]
  rw [abs_mul, abs_of_pos positive]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt positive)
  calc |a * Real.cos (frequency * t) + b * Real.sin (frequency * t)|
      ≤ |a * Real.cos (frequency * t)| + |b * Real.sin (frequency * t)| := abs_add_le _ _
    _ = |a| * |Real.cos (frequency * t)| + |b| * |Real.sin (frequency * t)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |a| * 1 + |b| * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left cosine (abs_nonneg a))
          (mul_le_mul_of_nonneg_left sine (abs_nonneg b))
    _ = |a| + |b| := by ring

end Synthesis.Domains.Electronics.SecondOrder
