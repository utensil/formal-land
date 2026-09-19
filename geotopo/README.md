# Geometric topology route map

Open [geotopo-route-map.html](geotopo-route-map.html) directly in a browser. All
styles, scripts and data are embedded; the map and charts work offline.

The diagram places our contributions within 78 milestones across all 11 layers
of the GeometricTopology roadmap. Four goals group work by shared infrastructure:

- **Knot surgery and concordance:** one presentation/equivalence trunk branches
  toward Property P and Freedman's topological slicing theorem.
- **Diffeomorphisms and manifold gluing:** Whitney topology and smooth families
  branch toward Smale–Hatcher and Li's rank-versus-Heegaard-genus counterexample.
- **Smooth / PL / Top structures:** realization branches toward Whitehead
  comparison, Manolescu's statement and the open Zeeman conjecture.
- **Geometric three-manifolds:** surgery and hyperbolic geometry branch toward
  Geometrization, Weeks minimum-volume and Agol virtual-fibering statements.

Each card renders an explicit nested `tree`, with shared work packages in the
trunk and distinct targets at the leaves. Clicking a tree node exposes its
milestones and navigation to the full map. The six major proof endpoints remain
in `summits`; a merged goal can have several. Card trees summarize common work,
while the full dependency graph retains cross-links and separate deep inputs.

Statement gates remain intermediate to proof endpoints; gauge theory, parametric
sphere topology, four-dimensional disk embedding and Ricci flow are explicit
proof dependencies. The source roadmap targets statements; the proof horizons
are editorial long-term extensions, not claims about existing implementations.

Each route also has four inspectable checkpoints in `data/roadmap.json`. They
can represent parallel branches, rather than sequential stages. A checkpoint is
met only when all its listed milestones are available. A proof milestone needs
explicit status and a `completionEvidence` source link; merging a contributing
PR cannot complete it automatically. Bars show milestone states, not merged-PR
fractions, effort or a percentage of mathematical completion. Shared work can
appear on several cards; the charts deduplicate the selected PR cohort.

The snapshot at **2026-09-19 17:08 UTC** preserves 139 public PR records:
134 currently labeled GeometricTopology PRs and five retained historical records.
The charts select 37 verified contributions: 20 merged, eight open and nine closed
without merging. Fourteen retain verified review attribution. Fourteen newly
mapped contributions include the current knot-invariant, Whitney-topology and
curvature work, plus earlier link and gluing attempts. Closed and relabeled
attempts remain visible; authorship does not imply review attribution.

Since the previous snapshot, #6396, #6486, #6781 and #7568 have merged. The eight
open contributions are #7552, #7559, #7577, #7579, #7588, #7592, #7595 and #7600;
all are labeled `awaiting-author` at collection. Chart volume density #7595 is
mapped from its title and changed source files; its public description currently
contains unrelated Whitney-topology text. That metadata error does not move it
to the Whitney milestone.

The three-manifold route now shows the curvature and volume work, and the knot
route shows the two invariant-preservation PRs. Merged pointwise curvature does
not establish a global volume measure or Ricci-flow development. The link-isotopy
handoff has advanced to presentation equivalence, invariant agreement and
complements. Missing or partial exact-head review evidence remains unscored.

## Data and updates

- `data/roadmap.json`: pinned roadmap sources, milestone scope, dependencies,
  diagram layout, route trees, frontiers, summit criteria and checkpoints. Update these editorial interpretations
  when a new contribution changes the available API or next handoff.
- `data/selection.json`: explicit PR-to-milestone mapping and worked/reviewed
  attribution. A reviewed marker requires a public evidence link. Authorship
  alone never establishes review attribution.
- `data/prs.json`: public metadata and preserved review observations for every
  discovered labeled PR and retained historical record. The charts filter this
  archive to explicitly attributed contributions. The collector stores no comment bodies or credentials.
- `src/`: page template, shared SpinRep visual language and interaction code.
  `build.py` validates inputs and generates the standalone HTML deterministically.

From the repository root, with Python 3 and authenticated GitHub CLI available:

```sh
python3 geotopo/refresh.py --discover
# Add verified PRs and milestone mappings to data/selection.json.
python3 geotopo/refresh.py
python3 geotopo/build.py
python3 geotopo/build.py --check
python3 -m unittest discover -s geotopo/tests -v
node --check geotopo/src/app.js
node --test geotopo/tests/time.test.cjs
```

Discovery paginates all labeled GeometricTopology PRs and reports those without
milestone mappings. It does not infer worked/reviewed attribution.
Reviewed-only PRs require an explicit entry supported by review evidence. Refresh
updates new/open and changed terminal PRs, preserving unchanged terminal evidence;
use `--all` to recollect every retained PR. A failed request leaves the previous snapshot intact. Successive
refreshes preserve observations from edited comments and remove exact duplicates.
Always inspect changed scope, source links and route frontiers before committing.

## Reading the map and charts

Route chips filter colored paths and chart cohorts. The worked/reviewed lens
further narrows the selected contributions. Clicking a route, milestone or PR
point connects its activity to the relevant dependency and next handoff. The
collapsed PR table provides supporting records, rather than the main view.

All stored timestamps are UTC. The aligned charts use the browser's local
calendar and timezone for every label, tooltip, day boundary and time window.
Activity bins begin at local 00:00, 06:00, 12:00 and 18:00; their elapsed width
changes across daylight-saving transitions. The charts show stacked lifecycle
and workflow-stage transitions above, with PR review-health markers below. Circles mean
merged, diamonds closed, and triangles open. A dashed white ring marks verified
review participation. The orange line is a centered three-local-calendar-day median of merged
selected PRs, plotted at local noon (the day plus its two adjacent days). A dashed
continuation carries the last available median to the snapshot, with its source
day and sample count in the tooltip; it is not a new daily measurement. Open,
closed-unmerged and unscored PRs do not enter this median. Unassessed points have a separate lane.

Health follows the SpinRep public-review churn formula:
`max(0, 100 - (3A + 4D + 3H + 6L + 8B + 12S + 5U))`.
A is observed additional rounds; D distinct failing rubrics; H failing high-impact
rubrics; L rubrics failing across multiple rounds; B distinct blocking
rubric/round pairs; S explicitly recorded scope resets; U unresolved rubrics at
the snapshot head. A score requires a complete scoreboard for that exact head.
Missing, stale, pending or skipped evidence never becomes a perfect score or an
observed failure. This is a review-churn indicator, not proof correctness.

Public comments can be overwritten before collection, so historical evidence is
incomplete. The timeline records observed events, not a full immutable review
history. Reviewed attribution is a verified minimum, not a claim that unmarked
PRs received no review.

## Source and publication boundaries

The roadmap is pinned to `TauCetiProject/TauCetiRoadmap` commit
`d58f0b411ad04e1074ba20a69d1c5fb0c4b88da3`; source-context checks use
`TauCetiProject/TauCeti` commit `d520d747c7e3ec7be86a48d85329095a883fee8d`.
The 20 September (Singapore time) refresh verified that the pinned roadmap text is unchanged
at roadmap head `59c6b0bd3ce81d43f37a2cc4a20d8ee9333465ca`. The Whitney
coordinate milestone includes global-chart topology, manifold-source
vector-valued jets and normed-space smooth-family continuity. General target
charts and the general manifold map into `Diff(M)` remain separate open milestones.
The earlier global-chart Diff contribution closed without merging; the general
manifold-target Whitney topology in #7592 remains under review. Global
collar data is available, but global collar existence and gluing remain open.
The Zeeman statement and its cylinder API are available; the conjecture remains
open and is never counted as a proved summit.

Dependency links cite roadmap lines, not Lean import edges. Milestone scope is
an interpretation of these sources, not a fresh proof audit: chart-level Whitney
work is narrower than a global embedding theorem, and a contractibility predicate
does not prove Zeeman's conjecture.

Geotopo CI checks data, generated output and tests, then stages the HTML and this
README as `pages-geotopo`. Shared Pages deployment consumes successful main-branch
artifacts under `/geotopo/`; PR builds provide a review artifact.
