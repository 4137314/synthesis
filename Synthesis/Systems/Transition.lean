namespace Synthesis.Systems

/-- Discrete transition abstraction, including nondeterministic systems. -/
structure TransitionSystem (State : Type u) where
  initial : State → Prop
  step : State → State → Prop

inductive Reachable (system : TransitionSystem State) : State → Prop where
  | initial {s} : system.initial s → Reachable system s
  | step {s t} : Reachable system s → system.step s t → Reachable system t

structure Invariant (system : TransitionSystem State) (property : State → Prop) : Prop where
  initialized : ∀ s, system.initial s → property s
  preserved : ∀ s t, property s → system.step s t → property t

theorem Invariant.reachable {system : TransitionSystem State} {property : State → Prop}
    (proof : Invariant system property) {s} (h : Reachable system s) : property s := by
  induction h with
  | initial h => exact proof.initialized _ h
  | step _ h ih => exact proof.preserved _ _ ih h

/-- Forward simulation with an explicit abstraction map. Stuttering can be modeled
by including identity steps in the abstract transition relation. -/
structure Simulation (concrete : TransitionSystem C) (abstract : TransitionSystem A)
    (observe : C → A) : Prop where
  initial : ∀ s, concrete.initial s → abstract.initial (observe s)
  step : ∀ s t, concrete.step s t → abstract.step (observe s) (observe t)

theorem Simulation.reachable {concrete : TransitionSystem C} {abstract : TransitionSystem A}
    {observe : C → A} (simulation : Simulation concrete abstract observe)
    {s} (h : Reachable concrete s) : Reachable abstract (observe s) := by
  induction h with
  | initial h => exact .initial (simulation.initial _ h)
  | step _ h ih => exact .step ih (simulation.step _ _ h)

theorem Simulation.safety {concrete : TransitionSystem C} {abstract : TransitionSystem A}
    {observe : C → A} (simulation : Simulation concrete abstract observe)
    {property : A → Prop} (invariant : Invariant abstract property)
    {s} (h : Reachable concrete s) : property (observe s) :=
  invariant.reachable (simulation.reachable h)

end Synthesis.Systems
