# Engineering model catalog

Every row below describes implemented Lean definitions, not an assertion that a full
engineering discipline is supported. Scalars are exact rationals unless indicated
otherwise; `RealElectronics` and the analytic electronics package explicitly use Mathlib
real, complex and ordered-field theory. Quantities use coherent SI units. Rational
models do not approximate a real-valued system with an error bound; no such
approximation theorem is provided.

Physical modeling laws are definitions and explicit hypotheses. Their consequences
are proved, while their applicability to a real device remains an engineering premise.
No project-specific global logical assumptions are introduced.

## Electronics

The electronics domain has two layers. `Synthesis.Domains.Electronics` is exact,
rational and independent of Mathlib: it holds every element whose coefficients are
stored as exact IR parameters, and it is itself decomposed into `Electronics.Exact.{Units,
Resistor, Capacitor, Inductor, Source}`. `Synthesis.Domains.Electronics.Analytic` is the
umbrella of the analytic layer and uses Mathlib for ordered fields, real calculus and
complex numbers. See [ADR 0005](adr/0005-electronics-domain-package.md) for the boundary
between the layers and [ADR 0006](adr/0006-electronics-module-decomposition.md) for the
decomposition of each layer into one module per theory.

All elements are ideal and isothermal. Unless a module says otherwise the description
is a fixed operating point: there is no temperature coefficient, ageing, tolerance,
parasitic, noise or breakdown model anywhere in this domain, and no theorem below
asserts that a fabricated device obeys the equation it is proved about.

### Exact rational elements

`Synthesis.Domains.Electronics` defines a constant resistor with `R ≥ 0`, a conductor
with `G ≥ 0`, a capacitor with `C > 0`, an inductor with `L > 0` and the two ideal
independent sources. The constitutive laws are `V = R I`, `I = G V`, `q = C V` and
`φ = L I`, with passive-sign power `P = V I`; see [Ohm's law](https://openstax.org/books/university-physics-volume-2/pages/9-4-ohms-law),
[electrical power](https://openstax.org/books/university-physics-volume-2/pages/9-5-electrical-energy-and-power)
and [capacitance and energy storage](https://openstax.org/books/university-physics-volume-2/pages/8-4-energy-stored-in-a-capacitor).
Storage elements exclude the degenerate zero coefficient so that stored charge
determines voltage and flux linkage determines current.

Proved: `joule_law`, `passive`, `voltage_additive`, `voltage_homogeneous`, `voltage_odd`,
`power_even`, `power_eq_zero_iff`, `power_positive`, `short_circuit`, `zero_current`,
`series_voltage`, `series_power`, `series_comm`, `series_assoc`, `series_zero`,
`series_upper_bound`, `loop_voltage_balance`, `conductor_joule`, `conductor_passive`,
`parallel_current`, `parallel_power`, `parallel_comm`, `parallel_assoc`, `parallel_open`,
`reciprocal_resistance`, `ohm_dual`, `source_loop_operating_point`, `source_power_balance`,
`voltage_divider`, `voltage_divider_solved`, `current_divider`, `charge_additive`,
`charge_zero`, `capacitive_energy_nonnegative`, `capacitive_energy_even`,
`capacitive_energy_charge`, `capacitive_energy_zero_iff`, `parallel_charge`,
`parallel_capacitive_energy`, `flux_additive`, `inductive_energy_nonnegative`,
`inductive_energy_even`, `inductive_energy_flux`, `series_flux`, `series_inductive_energy`,
`elastance_capacitance`, `series_capacitor_voltage` and `operating_point_exists`, plus
the dimensional identities `ohm_dimensions`, `power_dimensions`, `conductance_dimensions`,
`capacitance_dimensions`, `inductance_dimensions`, `energy_dimensions`,
`resistance_conductance_dual`, `charge_dimensions`, `work_dimensions`, `flux_dimensions`,
`rc_time_dimensions` and `lr_time_dimensions`.

Also proved: `power_mono` (dissipation is monotone in the resistance at a fixed
operating current), `parallel_lower_bound`, `dual_power`, `charge_injective` and
`flux_injective` (stored charge determines terminal voltage and flux linkage determines
branch current, which is what excluding the degenerate coefficient buys),
`inductive_energy_zero_iff`, `parallel_capacitance_comm`, `parallel_capacitance_assoc`,
`series_capacitor_energy`, `series_inductance_comm`, `series_inductance_assoc`,
`inverse_inductance_product`, `parallel_inductor_current` (the division-free parallel
inductance law), `VoltageSource.delivered_odd`, `CurrentSource.delivered_odd`,
`VoltageSource.dead_delivers_nothing`, `CurrentSource.dead_delivers_nothing`,
`source_loaded_delivers` and `source_node_operating_point` (the dual solved circuit: an
ideal current source across a strictly positive conductance).

`source_loop_operating_point` is an existence *and* uniqueness statement for the loop
current of a source driving one strictly positive resistance. Divider identities are
stated in cleared-denominator form and hold without a nondegeneracy hypothesis; the
solved form `voltage_divider_solved` requires a nonzero loop resistance. Series
capacitance and parallel inductance are expressed through reciprocal parameters
(`elastance`) so that the laws stay additive and division free.

`Components.resistor`, `Components.conductor`, `Components.capacitor`,
`Components.inductor` and `Components.voltageSource` bind these coefficients into IR
schema 3 exact parameter defaults. `resistor_passive`, `conductor_passive`,
`capacitor_energy_nonnegative` and `inductor_energy_nonnegative` are unconditional
certificates; `source_delivers` is conditional on a stated current direction, because an
ideal source is active and has no passivity theorem. Tests cover negative current,
positive dissipation, rejection of negative resistance and conductance, rejection of
degenerate capacitance and inductance, dimension mismatch and altered coefficients.

### Thévenin equivalence of a one-port

`Electronics.Thevenin` models an affine one-port `v = e + r i` in the passive convention.
The family contains the ideal voltage source (`r = 0`), the ideal resistor (`e = 0`) and
every Thévenin or Norton source; see
[Thévenin's theorem](https://en.wikipedia.org/wiki/Th%C3%A9venin%27s_theorem).

Proved: `affine_feasible`, `affine_resistor`, `affine_voltageSource`, `affine_thevenin`,
`affine_norton`, `affine_series`, `affine_parallel`, `affine_open_circuit`,
`affine_unit_current`, `affine_unique`, `affine_identified`, `affine_passive_iff` and
`affine_not_passive`. `affine_series` and `affine_parallel` prove that the family is
closed under both interconnections, with the Millman form for the parallel equivalent, so
any one-port assembled from independent sources and resistances by series and parallel
composition presents an affine driving point. `affine_unique` proves that two affine
one-ports no terminal measurement distinguishes have the same parameters, which is what
licenses identifying a source from its open-circuit voltage and its terminal slope, and
`affine_passive_iff` proves that an affine one-port is passive exactly when it is a plain
resistor with nonnegative resistance. A bridge is not reachable by series and parallel
composition, so the general network form of Thévenin's theorem is not established here.

### Two-terminal elements and interconnection

`Electronics.Element` models an element as its set of admissible `(v, i)` pairs over an
arbitrary ordered field, which is what ideal sources require: they are not functions of
their terminal variables. It defines `resistor`, `conductor`, `voltageSource`,
`currentSource`, `openCircuit`, `shortCircuit`, `thevenin` and `norton`, the
`series`/`parallel` interconnections, and the predicates `Passive`, `Lossless` and
`Feasible`.

Proved: `resistor_passive_iff` and `conductor_passive_iff` (passivity is *equivalent* to
a nonnegative coefficient), `voltage_source_not_passive`, `current_source_not_passive`,
`open_lossless`, `short_lossless`, `resistor_conductor_dual`, `resistor_zero_short`,
`conductor_zero_open`, `thevenin_zero`, `thevenin_norton`, `series_comm`, `series_assoc`,
`parallel_comm`, `parallel_assoc`, `series_resistor`, `parallel_conductor`,
`series_short`, `parallel_open`, `series_current_source`, `parallel_voltage_source`,
`series_passive`, `parallel_passive`, `passive_of_equivalent`, `series_power_split` and
`parallel_power_split`. Sign conventions are explicit: `absorbed` is passive, `delivered`
is active, and both source models are declared in the active orientation.

### Resistive interconnection algebra

`Electronics.Resistive` gives closed forms for the standard resistive networks:
`parallel` (product over sum), `series`, `dividerVoltage`, `dividerCurrent`, the
Wheatstone `bridge`, and the delta-wye pair `wyeBranch`/`deltaTerminal`; compare
[series and parallel resistors](https://openstax.org/books/university-physics-volume-2/pages/10-3-resistors-in-series-and-parallel).

Proved: `parallel_comm`, `parallel_assoc`, `parallel_zero`, `parallel_reciprocal`,
`parallel_self`, `divider_kvl`, `divider_kcl`, `divider_ohm`, `bridge_balanced_iff`,
`bridge_balanced_products`, `delta_wye_terminal`, `wye_branch_comm`, `parallel_pos`,
`parallel_lt_left`, `parallel_lt_right`, `le_series_left`, `le_series_right`,
`parallel_le_quarter_series`, `parallel_mono_left`, `divider_bounds`, `divider_mono` and
`wye_branch_pos`. `delta_wye_terminal` proves that the wye equivalent reproduces the
terminal resistance of the delta, which is what makes the transformation admissible
inside a larger network; `bridge_balanced_iff` characterizes the null condition.

### Kirchhoff's laws and Tellegen's theorem

`Electronics.Network` models a lumped interconnection as a finite directed multigraph
with `incidence`, `branchVoltage`, `injection` and `KCL`. The model is quasi-static:
radiation, mutual coupling and distributed effects are outside it.

Proved: `incidence_column_sum`, `incidence_potential`, `self_loop_voltage`,
`injection_total`, `tellegen_general`, `tellegen`, `power_conservation`,
`kvl_closed_walk`, `kvl_branch_walk`, `kcl_add`, `kcl_smul` and `kcl_zero`, together
with `ResistiveSolution.branch_power`, `dissipation_nonnegative`,
`dissipation_eq_injection`, `dissipation_zero_of_kcl` and `branch_dissipation_zero`.
Tellegen's theorem is proved in its strong form: the potentials and the currents may
come from different operating points and different constitutive laws, provided they
share the topology; see [Tellegen's theorem](https://en.wikipedia.org/wiki/Tellegen%27s_theorem).
Kirchhoff's voltage law holds by construction because branch voltages are potential
differences, and `kvl_branch_walk` telescopes it along an oriented closed walk.

### Nodal analysis

`Electronics.Nodal` defines the nodal `operator` sending node potentials to injected
currents, and `Solves` for a given injection pattern.

Proved: `operator_add`, `operator_smul`, `operator_constant`, `operator_shift`,
`superposition`, `kcl_of_source_free`, `power_identity`, `branch_voltage_zero`,
`branch_voltage_unique`, `current_unique` and `dissipation_unique`. The uniqueness
results assume strictly positive branch conductances; under that hypothesis two
potential assignments with the same injections have identical branch voltages and
currents, so the reference-node offset is the only unobservable freedom. A network
containing an active element does not satisfy the hypothesis.

### Source equivalence and power transfer

`Electronics.Source` solves a Thévenin source loaded by a resistance: `loadCurrent`,
`loadVoltage`, `loadPower`, `sourcePower` and `efficiency`; see
[maximum power transfer](https://en.wikipedia.org/wiki/Maximum_power_transfer_theorem).

Proved: `operating_point_unique`, `load_ohm`, `load_power_terminal`, `power_split`,
`short_circuit_current`, `open_circuit_no_current`,
`internal_resistance_from_measurements`, `superposition`, `homogeneity`,
`load_power_nonneg`, `maximum_power_transfer`, `matched_load_power`,
`efficiency_eq_power_ratio`, `matched_efficiency`, `efficiency_le_one`,
`efficiency_mono`, `dead_source_absorbs` and `live_source_delivers`. The maximum power
bound `E² / (4 R)` is proved for every nonnegative load and shown to be attained at the
matched load, and `matched_efficiency` proves that matching gives exactly one half
efficiency. Reproducing terminal behaviour licenses no claim about where inside a real
device the dissipation occurs.

### Energy storage in continuous time

`Electronics.Storage` states the capacitor and inductor laws as differential relations
over real time: `i = dq/dt` and `v = dφ/dt`, with `Capacitor.energy = C v² / 2` and
`Inductor.energy = L i² / 2`.

Proved: `energy_nonneg`, `energy_eq_zero_iff`, `energy_charge`, `energy_flux`,
`constant_voltage_no_current`, `constant_current_no_voltage`,
`current_eq_capacitance_mul_rate`, `voltage_eq_inductance_mul_rate`, `hasDerivAt_energy`
for both elements, `energy_integral`, `charge_integral`, `parallel_constitutive`,
`parallel_energy`, `series_constitutive` and `series_energy`. The energy theorems are
the substance of the module: instantaneous absorbed power is exactly the derivative of
the stored energy, and its integral over an interval is the energy difference between
the endpoints. Dielectric loss, leakage, saturation and hysteresis are not modelled.

### Scalar linear differential equations

`Electronics.Ode` isolates the mathematics that every linear time-invariant circuit
reduces to: `x' = a x`. Proved: `hasDerivAt_exponential`, `exponential_linear`,
`linear_unique`, `linear_determined`, `linear_zero`, `linear_sign`, `linear_add` and
`linear_smul`. Nothing in the module is electrical; it carries no operating envelope and
no idealization of its own. `Transient` instantiates it at the coefficient `-1 / τ` and
`SecondOrder` uses it once for each factor of the characteristic polynomial.

### First-order transients

`Electronics.Transient` gives the closed-form relaxation `x(t) = x₀ e^{-t/τ}` and the
step response, with `ofRC` and `ofRL` computing the time constant; see
[RC circuits](https://openstax.org/books/university-physics-volume-2/pages/10-6-rc-circuits).

Proved: `natural_zero`, `step_zero`, `step_natural`, `natural_time_constant`,
`hasDerivAt_natural`, `natural_ode`, `natural_unique`, `hasDerivAt_step`,
`natural_antitone`, `natural_bounded`, `natural_tendsto_zero`, `step_tendsto_final` and
`rcConstitutive`. `natural_unique` proves that every differentiable trajectory obeying
`τ x' + x = 0` equals the closed form of its own initial value, so the solution is the
model's only behaviour rather than a guess. `rcConstitutive` connects the closed form to
the capacitor law of `Electronics.Storage` instead of assuming the circuit equation.

### Second-order transients

`Electronics.SecondOrder` models `x'' + a x' + b x = 0` with nonnegative dissipation and
strictly positive stiffness, parameterized by the two ODE coefficients so that the circuit
constructors stay division free. The engineering vocabulary is derived:
`naturalFrequency`, `dampingRatio`, `decayRate`, `dampedFrequency`; see
[RLC circuits](https://en.wikipedia.org/wiki/RLC_circuit).

Proved: `naturalFrequency_positive`, `naturalFrequency_sq`, `dampingRatio_nonneg`,
`dissipation_eq`, `dampingRatio_sq`, `discriminant_eq`, `characteristic_completed`,
`solves_add`, `solves_smul`, `mode_zero`, `hasDerivAt_mode`, `mode_solves`,
`sqrt_discriminant_sq`, `characteristic_slowRoot`, `characteristic_fastRoot`, `root_sum`,
`root_product`, `slowRoot_negative`, `fastRoot_negative`, `roots_distinct`,
`overdamped_decomposition`, `characteristic_doubleRoot`, `criticalMode_zero`,
`hasDerivAt_criticalMode`, `critical_solves`, `no_real_root`, `dampedFrequency_positive`,
`dampedFrequency_sq`, `oscillatoryMode_zero`, `hasDerivAt_oscillatoryMode`,
`oscillatory_solves` and `oscillatory_envelope`.

The three regimes are separated exactly by the sign of the discriminant.
`overdamped_decomposition` is the substantive result: *every* solution of an overdamped
relaxation is a combination of its two exponential modes, so the mode family describes all
behaviours rather than merely supplying some. `slowRoot_negative` and `fastRoot_negative`
prove that both real modes decay, which is the stability statement. `no_real_root` proves
that below critical damping no exponential mode exists at all, so the response necessarily
oscillates, and `oscillatory_envelope` bounds the ringing by its exponential envelope. The
underdamped regime has no completeness theorem: `oscillatory_solves` verifies the decaying
sinusoid family but does not prove it exhausts the solutions.

### Second-order circuits

`Electronics.Rlc` derives the governing equations of the series loop and the parallel node
from the element laws of `Electronics.Storage` together with one Kirchhoff constraint,
by differentiating the Kirchhoff identity and eliminating the remaining state variable.

Proved: `series_loop_solves`, `parallel_node_solves`, `series_discriminant`,
`series_overdamped_iff`, `parallel_discriminant` and `parallel_overdamped_iff`. The
discriminant identities are stated with denominators cleared, so the design inequalities
`R² C > 4 L` for the series loop and `L > 4 R² C` for the parallel node hold without a
nondegeneracy hypothesis. Both circuits are source free; a driven circuit adds a forcing
term that is not modelled, and neither is parasitic resistance of the reactive elements.

### Sinusoidal steady state

`Electronics.Phasor` defines the element impedances, their series and parallel
combinations, `averagePower`, and the `SeriesRLC` branch with its `resonance` frequency
and `quality` factor; compare [RLC series circuits](https://openstax.org/books/university-physics-volume-2/pages/15-4-rlc-series-circuits).

Proved: `resistor_re`, `resistor_im`, `inductor_re`, `inductor_im`, `capacitor_re`,
`capacitor_im`, `capacitor_inverse`, `series_impedance_re`, `series_impedance_comm`,
`series_impedance_assoc`, `parallel_impedance_comm`, `series_passive`,
`average_power_nonneg`, `inductor_average_power`, `capacitor_average_power`,
`resistor_average_power`, `phasor_time_domain`, `impedance_re`, `impedance_im`,
`impedance_series`, `impedance_passive`, `resonance_positive`, `resonance_squared`,
`impedance_at_resonance`, `reactance_zero_at_resonance`, `resistance_le_norm`,
`resonance_minimizes_norm`, `quality_positive` and `quality_antitone`. The phasor model
presupposes a single angular frequency, linearity and decayed transients; it must not be
applied to a nonlinear element, and `phasor_time_domain` fixes its time-domain reading.

### Power in sinusoidal steady state

`Electronics.Power` keeps the time-domain and phasor descriptions separate.
`instantaneous_decomposition` proves that the product of a voltage and a current sinusoid
of the same frequency is exactly a constant plus a term at twice the frequency; complex
power `S = V conj(I) / 2` carries the dissipated power in its real part and the exchanged
power in its imaginary part. See
[AC power](https://en.wikipedia.org/wiki/AC_power).

Proved: `instantaneous_decomposition`, `resistive_instantaneous_nonneg`,
`complexPower_ohm`, `realPower_ohm`, `reactivePower_ohm`, `apparent_sq`,
`realPower_le_apparent`, `realPower_nonneg_of_passive`, `realPower_reactance`,
`reactance_of_realPower`, `abs_powerFactor_le_one`, `powerFactor_eq_one_iff`,
`realPower_powerFactor` and `realPower_eq_averagePower`. `apparent_sq` is the power
triangle `|S|² = P² + Q²` proved as an identity, and `reactance_of_realPower` is its
converse direction: an element dissipating nothing at a nonzero current has no resistive
part. The averaging step itself is **not** proved: the module decomposes the instantaneous
product exactly but takes no integral over a period, so the identification of the constant
term with the average is stated, not derived. `powerFactor` is the displacement factor
only; harmonics and distortion are outside the phasor model.

### First-order frequency response

`Electronics.Filter` gives the two single-pole transfer functions with squared magnitudes
stated through `Complex.normSq`, which keeps every proof rational: the half-power point is
the exact statement `normSq = 1/2` and no logarithm or decibel approximation appears.

Proved: `rcCutoff_positive`, `pole_nonzero`, `pole_normSq`, `lowPass_normSq`,
`highPass_normSq`, `complementary`, `lowPass_zero`, `highPass_zero`, `lowPass_cutoff`,
`highPass_cutoff`, `lowPass_le_one`, `highPass_le_one`, `lowPass_antitone`,
`highPass_monotone` and `lowPass_lt_one`. `complementary` proves that the two responses
sum to unit power at every frequency, and `lowPass_antitone` proves monotone roll-off, so
the stop band is genuinely a stop band. Component tolerance, loading by the following
stage and noise are not modelled; a filter realized from these transfer functions is a
specification, not a circuit.

### Nonlinear devices

`Electronics.Semiconductor` implements the Shockley diode equation
`I = I_s (exp (V / n V_T) - 1)` and the square-law long-channel transistor; see
[the diode equation](https://en.wikipedia.org/wiki/Shockley_diode_equation) and
[MOSFET operating regions](https://en.wikipedia.org/wiki/MOSFET#Modes_of_operation).

Proved: `Diode.current_zero`, `current_strictMono`, `current_injective`,
`current_pos_iff`, `passive`, `reverse_saturation`, `current_voltage`,
`hasDerivAt_current`, `conductance_positive`, `conductance_operating_point`, and
`Mosfet.saturation_nonneg`, `cutoff`, `pinch_off_continuous`, `saturation_strictMonoOn`,
`hasDerivAt_saturation`, `transconductance_squared`, `hasDerivAt_triode` and
`channel_conductance`. `pinch_off_continuous` proves that the piecewise transistor model
has no jump at the boundary between its regions, and `conductance_operating_point` is
the small-signal identity `g = (I + I_s) / n V_T`. Both models are static and
isothermal; breakdown, high-injection, series resistance, channel-length modulation,
velocity saturation and self-heating are excluded.

### Feedback and operational amplifiers

`Electronics.Feedback` proves the properties of the memoryless loop gain
`A / (1 + A β)` and derives the two classical amplifier configurations from the
finite-gain device equation together with the input node equation.

Proved: `closedLoop_positive`, `closedLoop_le_forward`, `closedLoop_equation`,
`hasDerivAt_closedLoop`, `sensitivity_relative`, `closedLoop_tendsto`,
`OpAmp.inverting_closed_form`, `inverting_ideal_limit`, `non_inverting_ideal` and
`buffer_ideal`. The ideal gains are limits of the finite-gain closed forms, not
postulates. Everything is static: frequency response, slew rate, offset, saturation and
loop stability are not modelled, and no theorem here implies that a physical loop with
these parameters is stable.

### Magnetic coupling and transformers

`Electronics.Magnetics` models a pair of coupled inductors by its stored energy
`(L₁ i₁² + 2 M i₁ i₂ + L₂ i₂²)/2` and the ideal transformer by its turns-ratio
constraints; see [mutual inductance](https://openstax.org/books/university-physics-volume-2/pages/14-1-mutual-inductance).

Proved: `Coupled.energy_flux`, `energy_uncoupled`, `energy_nonneg`, `coupling_bound`,
`energy_nonneg_iff`, `couplingCoefficient`, `abs_coupling_le_one`, `coupling_one_iff`,
and `IdealTransformer.power_conserved`, `impedance_reflection`, `unit_ratio`,
`cascade_voltage`. `energy_nonneg_iff` proves that the coupling bound `M² ≤ L₁ L₂` is
*equivalent* to passivity of the pair, so it is a characterization rather than an added
assumption, and `abs_coupling_le_one` is its engineering form `|k| ≤ 1`. The ideal
transformer conserves power at every operating point and reflects a load by the square
of the turns ratio. Leakage, winding resistance, core loss and saturation are excluded.

### Two-port networks

`Electronics.TwoPort` describes a linear two-port by its impedance parameters and,
separately, by its transmission parameters; see
[two-port networks](https://en.wikipedia.org/wiki/Two-port_network).

Proved: `Impedance.absorbed_quadratic`, `open_circuit_primary`, `open_circuit_transfer`,
`series_absorbed`, `series_reciprocal`, `tee_reciprocal`, `tee_realizes`,
`input_impedance_loaded`, `passive_of_definite`, `definite_of_passive`, `passivity_iff`,
`input_nonneg_of_passive`, and `Transmission.determinant_cascade`, `cascade_reciprocal`,
`identity_reciprocal`, `cascade_identity`, `identity_cascade`, `cascade_assoc`,
`seriesImpedance_reciprocal`, `shuntAdmittance_reciprocal`, `seriesImpedance_cascade` and
`l_section_reciprocal`. `passivity_iff` characterizes passivity of a two-port with
positive input impedance by definiteness of its port quadratic form; `tee_realizes`
shows that reciprocity is exactly the condition for the three-element T realization; and
`cascade_reciprocal` shows that the transmission determinant identity survives cascading.

`Electronics.TwoPort.Admittance` is the dual description `i = Y v`, kept separate because
its natural algebra differs: admittance parameters add under *parallel-parallel*
interconnection and the three-element realization of a reciprocal port is the Π network.
Proved: `absorbed_quadratic`, `short_circuit_primary`, `short_circuit_transfer`,
`parallel_current`, `parallel_absorbed`, `parallel_reciprocal`, `parallel_comm`,
`parallel_assoc`, `pi_reciprocal`, `pi_realizes`, `output_admittance_loaded`,
`passive_of_definite`, `definite_of_passive`, `passivity_iff`, `input_nonneg_of_passive`
and `parallel_passive`.

`Electronics.TwoPort.Conversion` supplies the changes of coordinates, each with its
nondegeneracy hypothesis: a two-port has an admittance description only when its impedance
determinant is nonzero and a transmission description only when its transfer impedance is
nonzero. Proved: `toAdmittance_primary`, `toAdmittance_secondary`,
`toAdmittance_determinant`, `toAdmittance_determinant_inv`, `toImpedance_toAdmittance`,
`toAdmittance_reciprocal`, `transmission_determinant`, `toTransmission_reciprocal_iff`,
`toTransmission_reciprocal` and `tee_transmission_cascade`. Each conversion is proved
correct at the terminals, that is by reproducing the port variables, rather than by
asserting that the matrices invert; `toTransmission_reciprocal_iff` shows that the
transmission identity `AD - BC = 1` is exactly impedance reciprocity `z₁₂ = z₂₁`, and
`tee_transmission_cascade` checks the T realization against the ladder of transmission
elements instead of trusting that the two catalogs agree.

### Logic gates and static logic levels

`Electronics.Digital` separates the Boolean function computed by a gate from the
electrical discipline that lets a voltage stand for a Boolean value.

Proved: `nand_not`, `nand_and`, `nand_or`, `nand_implication`, `nor_not`, `nor_or`,
`de_morgan_and`, `de_morgan_or`, `multiplexer_low`, `multiplexer_high`, `majority_comm`,
`majority_idempotent`, `fullAdder_correct`, and for the level discipline
`marginLow_nonneg`, `marginHigh_nonneg`, `interpret_unambiguous`, `interpret_forbidden`,
`interpret_driven_low`, `interpret_driven_high`, `noise_immunity_low` and
`noise_immunity_high`, plus `Complementary.no_static_path`, `low_input_pulls_up` and
`high_input_pulls_down`. The noise-immunity theorems are the reason digital logic
composes: a driven output survives interference bounded by the noise margin. Voltages
inside the forbidden band have no interpretation, which is a refusal to guess rather
than a third logic value. No timing, delay, dynamic power, metastability or hazard
analysis is present.

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
`Components.water_atoms_conserved` certifies the IR primitive. A missing-reactant
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
Resource fan-out rejection is an explicit connector-policy invariant, distinct from gate semantics.

## Electrothermal coupling

`Synthesis.Bridges.Electrothermal` assumes all ideal resistor dissipation is exported
as heat, without storage or other energy channels. `power_conserved`,
`heat_nonnegative`, and `heater_verified` prove conservation and passivity in this
explicit coupling model. Its IR primitive exposes electrical current and thermal
power ports and carries the resistance parameter. It is not a temperature predictor.

## Evidence and compilation

`Domains.Components` binds complete interfaces and coefficient values to their
interpretations. A changed parameter, dimension, port list or operation is unsupported
by that exact recognizer. `Semantics.Primitive.verify` transfers domain reasoning into
`Semantics.Verified`, requiring feasibility and universal conditional correctness.
`Synthesis.Examples.Assurance.design` exercises rich semantic frontend compilation.

Primitive models contain one reusable definition and no junctions. Composition of multi-node physical
models still requires explicit coupling interpretations and compatibility proofs;
these single-definition certificates do not establish arbitrary network correctness.

## Mathlib real-valued electronics

`Synthesis.Domains.RealElectronics` extends the ideal resistor model to Mathlib's `ℝ`.
It proves `joule_law`, `passive`, `series_power`, and `operating_point_exists` using
Mathlib arithmetic and ring normalization. It predates the layered electronics package
above and is kept as the smallest illustration of a real-valued domain model; the
generic results of `Electronics.Element` specialize to `ℝ` and cover the same ground.

Neither this module nor the analytic electronics package is a continuous-time simulator
or a discretization theorem. `Electronics.Storage` and `Electronics.Transient` prove
properties of stated differential relations and of one closed-form solution family;
they do not construct solutions for arbitrary networks, and no numerical error bound is
provided anywhere. Real-valued coefficients are not compilable into rational IR
literals without a separate representation or an explicit approximation contract.
Mathlib and its transitive dependencies are pinned, and `scripts/cache.sh` fetches
exactly the import closure these modules use.


## Schema 3 representation and conservative terminal adapter

The existing exact certificates in Domains.Components and Bridges.Electrothermal now
use IR.Definition, symbolic-capable IR.Parameter and complete module recognizers.
Calculated quantities are relational observations, not fabricated input/output causality.
Their original laws, feasibility witnesses and conditional guarantees are unchanged.
The rich source/IR link in Examples.Assurance proves denotation preservation and
requirement declaration retention; retention alone is not a requirement encoding theorem.

Semantics.Conservative defines across-variable equality and signed through balance for
an arbitrary list of terminals. `Conservative.balanced` is its balance consequence.
This is a stated junction law, not empirical evidence for an arbitrary connector.
The domain must choose compatible quantities and orientation. Structural incidence
checking in IR.Connector is deliberately separate from this semantic predicate.

Electronics.Interface provides a reusable resistorDefinition with two acausal terminals,
a symbolic resistance parameter and explicit Ohm/terminal-balance term equations.
resistorIR binds that parameter without duplicating the definition. The model assumes
an ideal memoryless resistor, coherent units and currents entering the device; junction
currents have the opposite sign. `resistor_meaning` identifies the model relation,
`ohm_compatible` relates it to the established exact voltage law, and `resistor_verified`
proves feasible nonnegative absorbed power using the existing passivity theorem.
This does not prove arbitrary network assembly correct, nor automatically connect an
IR junction list to the separate analytic Network topology. Such an assembly/lowering
needs an explicit incidence/orientation mapping and preservation theorem.

QuantityKind/KindQuantity and AffineUnit distinguish semantic kinds, dimensions and
affine source coordinates. AffineUnit.normalize implements the declared rational scale
and offset with a nonzero-scale premise. No comprehensive unit catalog, empirical unit
calibration, uncertainty arithmetic or numerical approximation theorem is introduced.
All architecture fixtures are representation/validation tests, not new physical theories
for hydraulics, RF, FEM, navigation or nuclear systems.


Design.System and Frontend.engineering_system provide source-level typed composition.
Each part retains its local observation space and covered model; projections, coupling
relations and constraint relations are explicit. System.behavior is their conjunction.
System.represented and compileSystem_preserves relate the lowered module to that source
semantics. No joint feasibility or physical applicability is inferred. Child module
metadata and root bindings survive wrapper definitions/instances, and identical child
definitions are shared. Examples.Assurance.pairedInventory checks two typed inventory
placements and an explicit initial-agreement law; duplicate placements are rejected.
