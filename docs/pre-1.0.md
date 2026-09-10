# Pre-1.0 technical criteria

A release date is not a stability argument. Before a 1.0 decision, require:

- Multiple independently maintained domains and backends to exercise the same schema
  across real release upgrades; in-repository fixtures are not independent adoption.
- A non-Lean implementation to pass the published wire conformance fixtures.
- Real transformation pipelines to retain revision-qualified trace/evidence across
  branching, specialization, migration and artifact encoding.
- Stable diagnostic categories and frontend name/source APIs through domain DSL use.
- Scale measurements on realistic hierarchy, behavior and geometry distributions,
  including validation cost and memory pressure, not just definition hash lookup.
- A published migration/deprecation practice demonstrated by actual consumers.
- A reviewed threat model and cryptographic fingerprint scheme for adversarial or
  distributed content-addressed use; FNV fingerprints are insufficient for this.
- Assurance reviews distinguishing source proofs, translation validation, encoding
  correctness and external tool reports.

Schema 3 is soft-frozen. Add representations through contracts, extensions, derived
views and interop objects first. No theorem claims the foundation can never need a
change. A necessary semantic change must have an ADR, migration, version decision,
conformance update and consumer-visible explanation.

Laptop-like and spacecraft-like projects require no new central ontology: their power,
thermal, software, control, structure and manufacturing definitions can live in separate
qualified namespaces, connect only through explicit interfaces, and branch into different
revisioned lowering pipelines. This is a structural/extension argument, not a claim that
Synthesis already supplies the engineering models or backends for those products.
