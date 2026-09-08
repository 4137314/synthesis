# Domain extension contract

A branch of engineering extends the kernel with a **theory**, not just a new domain
label. Use `IR.Domain.custom` for new branches; do not grow a central case split in
the compiler. An operation identifier should contain an owner namespace and semantic
version. The current graph stores this as a string; resolution is the interpreter's
responsibility and must inspect the full component interface.

Every theory should define and document:

1. Its observation space: states, trajectories, fields, distributions or another
   precise mathematical object; time and causality must be explicit where relevant.
2. Quantities and units: normalize units before IR construction. Equal SI exponents
   do not imply identical physical kinds (energy and torque, for example). Use
   distinct custom port types when the distinction matters. Affine temperature
   conversions, complex amplitudes and numerical approximations need explicit models.
3. Constitutive relations, conservation equations and admissibility conditions,
   including the operating envelope and all idealizations.
4. Component **and connection** interpretation. Unknown operations/interfaces return
   `none`; cross-domain couplings need a justified transducer interpretation.
5. Requirements as `Logic.Contract`, each with a stable project-level identifier and
   traceability to its source. `Semantics.Verified` is evidence for one requirement.
6. A feasibility witness and correctness proof for each certificate. For reactive
   applications add input receptiveness, progress/liveness and environment assumptions;
   the generic certificate does not establish them automatically.
7. Transition invariants or trace properties for safety requirements, with simulation
   proofs when abstracting a more detailed system.
8. Positive examples and negative regressions: unsupported operations, incompatible
   dimensions/interfaces, inconsistent laws and violated assumptions.

The common kernel never imports a domain package. Domain packages may depend on
Logic, Physics, Systems, IR and Semantics. Bridge packages may import two domains and
must own the coupling semantics. Examples and tests depend on those packages, never
the reverse. Keep package dependencies acyclic; promote abstractions into the kernel
only after independent domains demonstrate the same mathematical requirement.

Potential extensions include electronics, photonics, mechanics, thermal systems,
fluid systems, chemical processes, materials, control, robotics and quantum systems.
The initial implemented subset is documented in [models](models.md); the remaining
branches are extension targets. No promise of complete
coverage or correctness for arbitrary engineering follows from the kernel.

See `Synthesis/Examples/Assurance.lean` for an exact integer inventory model, a
non-vacuous conservation certificate, unsupported/inconsistent-model rejection and a
bounded discrete controller safety proof. These are small executable examples of the
method, not certified industrial designs.

AST schema 2 carries named rational literal parameters with SI dimensions. Use these
for component coefficients instead of hiding different coefficients behind identical
component identities. A `Semantics.Primitive` recognizer checks the complete component;
its relation may use typed domain parameters whose admissibility has already been proved.
New models and tests use explicit Lean variables (`autoImplicit false`) and English prose.
