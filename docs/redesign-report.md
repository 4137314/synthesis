# Schema 3 redesign report

The checked-out repository has been migrated to API 0.5.0 / IR schema 3. The flat
schema-2 compiler graph is removed. No target backend or external deployment was added.
The result is an implemented extension foundation, not a claim that every engineering
model can already be translated to every target or that future API evolution is finished.

1. **Current-state findings.** The previous IR conflated definitions and instances,
   supported only directed pairwise edges and rational coefficient records, and made
   the frontend a near-copy of that graph. Its independent relational mathematics,
   feasibility-bearing certificates and assumption audit were valuable. The full audit,
   caller map and dependency findings are in ADR 0007.

2. **Representation stack.** Domain-chosen rich Lean source → explicit lowering and
   denotation relation → canonical IR.Module → checked/interpreted boundaries →
   independent representation-changing stages/exporters.

3. **Module hierarchy.** Public Synthesis.IR, Semantics, Design, Frontend and Interop
   umbrellas expose focused modules. Domain adapters now have independent Electronics,
   Thermal, Mechanics, Photonics, Quantum and Chemistry modules. Components is only a
   convenience umbrella. Repository checks enforce the complete kernel layer direction.

4. **AST/IR.** Module, Definition, Instance, Port, Junction and nested Operation are
   orthogonal records/containers. TypeExpr, Term and recursive Data are open interchange
   structures with kernel-checked decidable equality. No Lean closures are stored in IR.

5. **Rich semantic model.** Design.Model retains source, relation, lowering,
   interpretation and an explicit denotation theorem. Design.Definition separates
   parameters, interface and state types. Requirements carry contracts, declarations,
   provenance and retention evidence. Declaration retention is not an encoding theorem.

6. **Extensions/dialects.** Explicit Extension configurations recognize types,
   literals, operation signatures, ports, junctions and semantic attributes. Application
   signatures see original terms as well as inferred types, supporting value-dependent
   type families. No domain/backend enum or global registry is required.

7. **Identifiers/hierarchy.** Symbol, QualifiedId and versioned ContractId have distinct
   roles. Definitions are shared; instances bind parameters. Scoped instance paths
   resolve to ports, with ResolvedEndpoint evidence. Recursive structural hierarchy,
   duplicate identities and dangling paths are rejected.

8. **Interfaces/junctions.** Ports have open interface/type/role contracts. Multiway
   junctions support optional signal, conservative and resource incidence policies.
   Relational observations are not mislabeled causal terminals. Physical junction laws
   are separately expressed by Semantics.Conservative and domain interpretations.

9. **Parameters/expressions.** Literals, symbolic inputs, derived applications and
   ordered defaults are typed. Unknown references/signatures and shadowed binders fail.
   KindQuantity distinguishes semantic kind from dimension; AffineUnit separates scale
   and offset. Concrete-parameter sufficiency is a separate Specialized boundary.

10. **Behavior.** Behavior remains relational. LocalRelation composes heterogeneous
    local spaces through explicit projections. Open nested operations retain equations,
    initialization, state, dynamics, faults, constraints and private structures without
    assuming they are executable or physically valid.

11. **Transformations/refinement.** Stage A B supports different representations.
    Establishes and andThen_establishes compose successful postconditions. Refines,
    Equivalent and RefinementCertificate distinguish behavioral inclusion, lifting and
    non-vacuity. Existing equivalent PreservingPass certificate transfer survives.

12. **Validation/diagnostics.** Structural, extension typing, semantic coverage and
    requirement verification are separate. diagnostics_iff, endpoints_resolve and
    infer_sound connect checks to propositions. Diagnostics carry stable codes, scope,
    entity, source, expected/actual data and remediation where available.

13. **Backend/interop API.** Exporter Source Artifact supplies a versioned target,
    prerequisite checker and evidence-gated emitter. Result includes disclosure and
    trace data; rich Obligation carries an actual proposition. External artifacts gain
    no automatic formal trust.

14. **Information sufficiency.** Requirements are source-indexed propositions.
    Exporter.rejects_unsatisfied proves missing prerequisites cannot reach emission
    through run. The polygon-information test inspects actual contracts/coordinates/
    layers, while explicitly making no claim of complete GDSII sufficiency. Projection
    loss, derivation, assumptions and obligations are represented separately.

15. **DSL.** engineering_system composes typed semantic models, explicit coupling/constraint
    relations and requirements; compileSystem_preserves proves source behavior preservation.
    Child module metadata/bindings survive explicit wrapper scopes. The lower-level
    engineering/Builder constructs declaration programs with reusable
    instances, bindings, ports, junctions and operations. Domain-specific Lean syntax can
    extend it without core edits; a private clock declaration tests that boundary.
    Inspection/check commands expose IR, hierarchy, interfaces, operations and diagnostics.

16. **Domain migration.** Exact domain and bridge adapters now use schema 3 and retain
    their established correctness/feasibility certificates. Independent analytic domain
    mathematics remains intact. No obsolete universal graph compatibility stack remains.

17. **Electronics.** Electronics.Interface adds a reusable symbolic resistor definition,
    two acausal terminals, explicit Ohm/balance equations and instance resistance binding.
    ohm_compatible connects to the established voltage law; resistor_verified reuses the
    existing passivity theorem. Observation-only capacitor/inductor models are clearly
    distinguished from dynamic terminal models.

18. **Versions.** Package/API 0.5.0; IR schema 3 is stored in Module and checked.
    Dialect contract versions are independent. Old schema decisions are marked superseded
    where appropriate. Dependency pins were unchanged.

19. **Tests.** Tests.Architecture exercises hierarchy/reuse, dangling/cyclic/duplicate
    rejection, symbolic versus literal sufficiency, value-dependent widths, unsupported
    attributes/types/operations, multiway signals/conservative/resource policies,
    local-space composition, quantity kinds and lossy heterogeneous projection.
    Tests.Targets retains concrete digital clock/reset/state, DAE/initialization,
    geometry/layers/placement/hierarchy, requirement provenance and FEM-boundary data.
    Existing engineering/electronics regressions and examples were migrated.

20. **Documentation.** README, architecture, domain author guide, model catalog and
    schema ADR were updated; backend author guide and this report were added. Public API
    extraction includes the new modules. Generated output/database and doc-gen4’s separate search-data cache are rebuilt so removed
    schema-2 declarations cannot remain in pages/search. CI still gates publication on
    proof checks and verified pages.

21. **Remaining work and limits.** No solver, serializer, target emitter, automatic
    causalizer, general parameter evaluator, hierarchy flattening pass/theorem or full
    domain surface-language elaborator is claimed. Base builders do not capture every
    source span automatically. Local connector checks do not prove complete hierarchical
    resource semantics. Connecting arbitrary IR junction networks to analytic Kirchhoff
    topologies needs an explicit assembly/orientation preservation theorem. Requirement
    syntax/contract encoding and physical applicability remain explicit obligations.
    These are implementation/proof responsibilities for specific extensions and stages,
    not implicit promises of universal direct translation.

22. **Verification actually executed.** Lean builds, proofs and documentation verification used nix develop. The
    baseline check passed before edits. Targeted lake builds were used during migration;
    temporary failures were repaired. Final successful verification commands were:

    ```sh
    nix develop --command bash scripts/check.sh
    nix develop --command lake build Tests.Architecture
    nix develop --command lake env lean /tmp/synthesis_domain_guide.lean
    nix develop --command python3 scripts/check_repository.py
    nix develop --command bash scripts/docs.sh
    git diff --check
    ```

    check.sh passed the repository closure/dependency checks (107 Lean modules), full
    Lake build (2837 jobs), runtime tests and Tests/Audit.lean. The audit permits only
    propext, Classical.choice and Quot.sound. The extracted domain-guide example passed.
    Documentation generation extracted 93 project modules and verified 94 public API
    pages and search data, including absence of obsolete schema-2 declarations. The
    pinned documentation SQLite dependency emits existing C const-qualifier warnings;
    generation and verification succeeded. No verification blocker remains.
