# Measured optimization playbook

## Benchmark ledger

Start every experiment with:

```sh
git rev-parse HEAD
lake --version
lake env lean --version
git status --short --branch
```

Use stable target roots and comparable warm/cold conditions:

```sh
/usr/bin/time -l lake build <target>
```

Record `phase,base_sha,root,modules,jobs,wall_s,user_s,sys_s,max_rss_bytes,
lake_bytes,result`. Vary parallelism only as its own experiment.

## Graph and cone manifests

Begin with import edges, then use Lean metadata for declaration names, kinds,
source spans, type dependencies, value/proof dependencies, private status, and
instance status. Save one manifest per root with closure count, excluded roots,
package roots, and the exact build command. Use type dependencies for public
definition boundaries and value dependencies for proof-side imports.

## Safe transformation order

For one bounded cone:

1. make proof-only imports private;
2. privatize proof-only subterms;
3. merge wrappers only if public names and source contracts remain stable;
4. remove reviewed imports and stale reverse-use edges;
5. run `lake shake` with explicit roots and inspect its deletion set;
6. profile and test narrowly scoped shortcut instances.

After each item, build the changed module, forward and reverse consumers, the
cone, and the final target. Classify failures as missing names, instances,
notation, tactics, macros, generated declarations, or reverse-use requirements;
do not blindly restore or delete imports.

## Resource and rollback gates

Prefer smaller cones and incremental artifacts before whole-repository builds.
Cap parallelism based on available memory and monitor swap and thermal state.
Treat OOM, sustained unsafe swap, or thermal exhaustion as a pause condition.
Treat a missing API, axiom change, ambiguous instance, >10% wall regression,
or >5% RSS regression as a revisit trigger; record evidence and continue an
independent safe experiment unless the user must choose a different objective.

Keep rejected experiments in the ledger with the reason and rollback commit.
