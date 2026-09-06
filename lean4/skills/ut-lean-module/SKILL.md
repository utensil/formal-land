---
name: ut-lean-module
description: Optimize a large Lean 4 repository with the module system and measured dependency, import, elaboration, CPU, and memory improvements while preserving its public and kernel-checked contract.
---

# ut-lean-module

Use this skill when a Lean 4 repository has slow builds, high CPU or memory
use, large import closures, generated theorem/proof wrappers, or expensive
editor environments. It is a measurement-led optimization workflow, not a
license to change mathematics or weaken verification.

## Optimization reality check

A successful build is not an optimization. Adding an import to make an
isolated target elaborate is a compatibility repair; it normally enlarges the
environment and must not be reported as a speed or memory win. Classify such
repairs separately and return to the last green baseline. Every optimization
claim requires comparable before/after measurements on the same roots, cache
state, invalidation state, and parallelism.

The reference FLT work followed a concrete loop, not ad-hoc target repairs:
modulize a small named cone; make proof-module and utility imports private;
privatize proof-only subterms; prune out-of-scope `attribute [-simp]` and
`[-instance]` entries; merge wrappers; run `lake shake` with all relevant
package roots; remove imports retained only for extra reverse-use edges; repair
the shaken cone; rerun the shake; then profile narrowly scoped shortcut
instances. Expand only after each loop is green. Prefer reproducible generated
or scripted transformations, and review their complete change set before
committing.

Do not substitute “build more modules” for this loop. If a target fails,
isolate and classify the failure, make the smallest evidence-backed repair, and
then resume optimization. If a candidate regresses, restore it and try the
next independent transformation or cone; do not turn the repair into the
result.

## Non-negotiable contract

- Work on a dedicated branch or worktree and preserve the exact baseline.
- Treat the kernel, theorem statements, axiom checks, public names, import
  visibility, generated artifacts, and deterministic instance/simp behavior as
  requirements.
- Never add `sorry`, hide an error behind a broad import, or import a theorem
  into its own proof.
- Make one conceptual transformation per reversible commit. Record the
  hypothesis, affected cone, metrics, checks, and rollback point.
- Do not stage unrelated work or expose credentials, local machine paths, or
  project-private material in reports.

## Workflow

1. **Hydrate the cache, then pin the baseline.** Obtain the repository's
   Mathlib/dependency build cache before compiling project modules, using the
   documented cache command and exact Lean/toolchain pair. Resolve a mismatch
   safely and verify any temporary alignment is restored. Record the commit,
   revisions, package roots, cache state, hardware, parallelism, and CI checks.
   Start with one controlled small portion: a named leaf or import-cone root
   whose closure can be counted and built independently, as in Kha's 100-module
   experiment. Add representative and expensive roots only after it is green.
   Measure warm and cold builds when feasible with `/usr/bin/time -l` or the
   platform equivalent. Record wall time, user/system CPU, peak RSS, job count,
   and disk.
2. **Map dependencies.** Build import and reverse-use graphs, then supplement
   them with declaration-level type/value dependencies. Identify definitions,
   instances, proof-only helpers, private declarations, generated companions,
   tactics, notation, and extension imports. Use compiler metadata for source
   spans; textual matching must not cut declarations.
3. **Introduce module boundaries.** Work from leaves upward. Separate reusable
   definitions and instances from proof implementation only when the public
   contract permits it. Preserve namespaces, section variables, `include`,
   notation, options, universes, and exact statements. Treat instances as
   reachability roots even when absent from proof terms.
4. **Reduce exported work.** In small measured steps, make proof-only imports
   private, privatize proof-only subterms, merge redundant theorem wrappers,
   remove imports outside the reviewed cone, and clean stale reverse-use edges.
   Retain imports required by tactics, macros, notation, generated declarations,
   extension modules, and instances. Use `lake shake` only after roots and
   package boundaries are explicit, and review every deletion.
5. **Profile hotspots.** Investigate typeclass search, elaboration, large
   environments, and unusually expensive modules. Add a shortcut instance or
   local alias only when it expresses the same structure, is narrowly scoped,
   remains deterministic, and improves the measured cone. Test for ambiguity
   and import-order sensitivity.
6. **Validate every step.** Build changed leaves, forward and reverse consumers,
   the representative cone, and the final root. Run axiom, linter, generated
   file, and API checks. Compare statements, exported names, import visibility,
   and resource metrics with the baseline. Revert or isolate changes without a
   reproducible benefit.
7. **Report and hand off.** Maintain a ledger with phase, commit, target roots,
   module/job counts, wall/CPU/RSS/disk metrics, checks, tradeoffs, and
   rollback. Use bounded parallelism and stop before OOM, unsafe swap growth,
   thermal exhaustion, or destructive cleanup.

## Concrete transformation loop

When the baseline already contains optimization work, do not restart by adding
imports or widening the cone. For one bounded manifest, generate the exact
module and reverse-use closure; apply one structural change (private proof
import, private proof subterm, wrapper merge, or reviewed attribute pruning);
build changed leaves plus forward and reverse consumers; then run `lake shake`
with every relevant package root and review its complete deletion set. Repair
shaken-cone failures, rerun the shaker until stable, and compare against an
equivalently invalidated baseline. Commit only a reproducible wall/CPU/RSS or
closure improvement. A compatibility repair may be committed for correctness,
but it closes no optimization phase and does not justify expanding the scope.
Expand only after this loop is green.

For long-running optimization campaigns, continue phase-by-phase for the
declared time budget (five hours when requested) or until the full repository
has been optimized. A failed or unsafe individual partition is a local
backoff: bisect it, lower parallelism, or move to an independent cone. It is
not permission to terminate the campaign while safe work remains.

## Conditional guidance

- Read [module-system.md](references/module-system.md) before changing imports,
  sections, private declarations, or statement/proof boundaries.
- Read [optimization-playbook.md](references/optimization-playbook.md) when
  setting up measurements, graph manifests, shaking, or hotspot experiments.
- For generated `attribute [-simp]` and `attribute [-instance]` blocks, remove
  only names proven out of scope; rebuild exact modules and reverse dependents.
  These are environment controls, not theorem hypotheses.
- A long expression in a theorem type may be semantically required. Formatting
  or API restatement is a separate task from build optimization.

## Attribution

This workflow is informed by Sebastian Ullrich's FLT optimization discussion:

- [Lean Zulip: Anthropic formalization code analyses](https://leanprover.zulipchat.com/#narrow/channel/416277-FLT/topic/Anthropic.20formalization.3A.20code.20analyses)
- [Kha's controlled FLT build exploration](https://mathstodon.xyz/@kha@functional.cafe/117217762820742699)

The links are attribution and starting points, not repository-specific
instructions. Apply the method to the current project's own build system and
public contract.
