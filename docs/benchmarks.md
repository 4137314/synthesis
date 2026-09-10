# Query and wire scale checks

Routine `lake test` covers generated 100- and 1,000-definition wide models, index lookup,
canonical lookup correspondence samples, hierarchy expansion and wire round trips.

Optional runs after `lake build`:

```sh
nix develop --command lake env lean --run scripts/benchmark.lean 10000
nix develop --command lake env lean --run scripts/benchmark.lean 100000
```

The script reports construction/indexing, lookup, traversal, encoding and decoding
wall-clock milliseconds. It forces each phase through a printed result before sampling
the next clock, so times include small terminal-output overhead. They are not CI pass
thresholds or stable performance promises. The runner permits 256 MiB wire input.

Index.findDefinition uses a derived hash map with proved agreement. Index.findEntity
and descend? use that table for definition transitions; local member lookup still
scans the relevant declaration list. Public query iteration retains declaration order.
Module.walkHierarchy builds a shared definition table and accumulates chunks instead
of repeatedly concatenating a growing output prefix.

The benchmark intentionally uses buildIndex on generated raw data. It does not measure
or certify full structural validation: uniqueness checking and other established
validators still have scan-heavy paths. Nor does it measure all deeply nested designs,
allocator peaks, process RSS, external backends or physical engineering workloads.
Those remain pre-1.0 performance qualification work.

The API 0.6.1 stabilization run completed both optional sizes: 100,000 definitions
produced 200,002 visited entities and 39,967,113 encoded bytes. The interpreted decoder
took about 136 seconds on that run, so this size remains opt-in. Exact observations,
commands and caveats are recorded in [the stabilization report](stability-report.md).
