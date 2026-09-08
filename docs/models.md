# Engineering model catalog

Every row below describes implemented Lean definitions, not an assertion that a full
engineering discipline is supported. Scalars are exact rationals unless indicated
otherwise; `RealElectronics` explicitly uses Mathlib real numbers. Quantities use coherent SI units. Rational models do not approximate a
real-valued system with an error bound; no such approximation theorem is provided.

Physical modeling laws are definitions and explicit hypotheses. Their consequences
are proved, while their applicability to a real device remains an engineering premise.
No project-specific global logical assumptions are introduced.

## Electronics

`Synthesis.Domains.Electronics` defines a constant resistor with `R ≥ 0`, signed current,
`V = R I` and passive-sign power `P = V I`. The law and its restricted applicability
follow the conventional ideal-resistor model; see [Ohm's law](https://openstax.org/books/university-physics-volume-2/pages/9-4-ohms-law)
and [electrical power](https://openstax.org/books/university-physics-volume-2/pages/9-5-electrical-energy-and-power).

Proved: `joule_law`, `passive`, `series_voltage`, `series_power`, `zero_current`, and
`operating_point_exists`. Series composition assumes shared current. The parameterized
`Components.resistor` binds resistance into the AST; `resistor_passive` certifies it.
Tests include negative current, positive dissipation and rejection of negative resistance.
No AC impedance, parasitics, temperature dependence, circuit solution or transient model.

## Thermal

`Synthesis.Domains.Thermal` defines a nonnegative lumped conductance and signed heat
rate `G (T_left - T_right)`. This is the steady linear conduction abstraction with
geometry absorbed into `G`; see [conduction](https://openstax.org/books/college-physics-2e/pages/14-5-conduction).
The observations are temperature differences in coherent units, not affine unit conversions.

Proved: `equilibrium`, `hot_to_cold`, `orientation_reversal`, `terminal_conservation`,
and `dissipative`. `Components.thermal_direction` certifies nonnegative left-to-right
heat flow under an explicit temperature-order assumption. Reversed temperatures are
covered by a negative test. No heat capacity, entropy model, radiation or heat equation.
Signed rational temperatures are mathematically allowed; absolute-temperature
admissibility must be imposed by applications that require it.

## Mechanics and materials

`Synthesis.Domains.Mechanics` defines uniaxial small-strain elasticity with positive
Young's modulus, `stress = E strain` and energy density `E strain² / 2`.
Its physical applicability is the linear elastic regime; see [elasticity and stress/strain](https://openstax.org/books/college-physics/pages/5-3-elasticity-stress-and-strain).

Proved: `energy_nonnegative`, `stress_strictly_monotone`, `stress_unique`, `energy_even`,
and `work_identity`. `Components.elastic_passive` supplies a feasibility witness and
nonnegative-energy certificate. Degenerate zero modulus is rejected. No plasticity,
fracture, fatigue, anisotropic tensor constitutive law or material microstructure.
Stress and energy density share dimensions; their roles remain distinct named outputs,
not a claim that dimension equality alone establishes physical-kind equivalence.

## Photonics

`Synthesis.Domains.Photonics` is a fixed-operating-point, single-input, incoherent
power-budget model with `T ≥ 0`, `R ≥ 0`, `T + R ≤ 1`. Transmitted, reflected and
absorbed powers are `T P`, `R P` and `(1 - T - R) P`; compare [beam splitter power and loss specifications](https://www.rp-photonics.com/beam_splitters.html).

Proved: `transmitted_nonnegative`, `reflected_nonnegative`, `absorbed_nonnegative`,
`power_conservation`, `no_gain`, and `lossless`. `Components.optical_conservation`
certifies the parameterized component. Tests include a lossy splitter and invalid
fractions. No phase, interference, scattering matrix, polarization or Maxwell model.
In particular, this power splitter must not be used as a quantum beam-splitter model.

## Chemistry

`Synthesis.Domains.Chemistry` uses finite lists of molecules with repeated entries.
A reaction replaces a reactant prefix while retaining its context. A weight function
can count atoms of a chosen element. `BalancedElements` requires balance for every
element, consistent with [balanced chemical equations](https://openstax.org/books/chemistry-2e/pages/4-1-writing-and-balancing-chemical-equations).

Proved: `Reaction.conserves`, `Reaction.parallel_balanced`, `network_inventory_invariant`,
and `reachable_elements_conserved`. The concrete `Water.formation` describes
`2 H2 + O2 → 2 H2O`; `Water.formation_balanced` checks both elements and
`Components.water_atoms_conserved` certifies the AST primitive. A missing-reactant
case is rejected. Lists give a restricted ordered operational model, not complete
multiset rewriting. No kinetics, concentrations, reaction energy, thermodynamic
favorability, safety or nuclear mass conversion is inferred from stoichiometry.

## Quantum

`Synthesis.Domains.Quantum` represents complex amplitudes with rational real and
imaginary parts. `Gate` requires complex linearity, a two-sided inverse and squared-norm
preservation. X, Z and S have explicit implementations and proofs, following the
standard [single-system gate framework](https://learning.quantum.ibm.com/course/basics-of-quantum-information/single-systems).

Proved: `Gate.preserves_normalization`, the obligations of `Gate.andThen`,
`x_involution`, `z_involution`, and `phase_squared`. `Components.quantum_normalization`
certifies a finite recognized gate catalog; tests include a nontrivial normalized
superposition. No Hadamard gate, arbitrary phase, measurement, entanglement or noise
model is implemented. Complex rationals exclude amplitudes such as `1 / sqrt(2)`.
AST quantum fan-out rejection remains a separate wiring invariant.

## Electrothermal coupling

`Synthesis.Bridges.Electrothermal` assumes all ideal resistor dissipation is exported
as heat, without storage or other energy channels. `power_conserved`,
`heat_nonnegative`, and `heater_verified` prove conservation and passivity in this
explicit coupling model. Its AST primitive exposes electrical current and thermal
power ports and carries the resistance parameter. It is not a temperature predictor.

## Evidence and compilation

`Domains.Components` binds complete interfaces and coefficient values to their
interpretations. A changed parameter, dimension, port list or operation is unsupported
by that exact recognizer. `Semantics.Primitive.verify` transfers domain reasoning into
`Semantics.Verified`, requiring feasibility and universal conditional correctness.
`Tests.Engineering.compiledResistor` exercises semantic frontend compilation.

Primitive models contain one node and no edges. Composition of multi-node physical
models still requires explicit coupling interpretations and compatibility proofs;
these single-node certificates do not establish arbitrary network correctness.

## Mathlib real-valued electronics

`Synthesis.Domains.RealElectronics` extends the ideal resistor model to Mathlib's `ℝ`.
It proves `joule_law`, `passive`, `series_power`, and `operating_point_exists` using
Mathlib arithmetic and ring normalization. This is an algebraic real-valued theory,
not a continuous-time simulator or a discretization theorem. Real-valued coefficients
are not yet compilable into rational AST parameters without a separate representation
or an explicit approximation contract. Mathlib and its transitive dependencies are pinned.
