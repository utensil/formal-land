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

The snapshot at **2026-09-14 02:49 UTC** includes 23 verified contributions:
16 merged, two open and five closed without merging. Fourteen have verified review
attribution, cross-checked against public review observations. Discovery checked
all 112 GeometricTopology PRs, recent utensil-authored PRs and the review desk's
published evidence; it found ten new authored contributions and no additional
reviewed-only PRs. Context milestones remain visible without importing unrelated
PRs into the charts.

The ten additions are #6355 (global collar data), #6396 (smooth link ambient
isotopy), #6435 (ordered cylinder and Zeeman statement), #6475 (link component
disjointness), #6486 (triangulability predicates), #6519 (closed circle-isotopy
attempt), #6524 (global-chart Diff topology), #6528 (Gauss-to-PD component
traversal), #6530 (mirror sign/writhe compatibility), and #6531 (diffeotopy group
packaging). The previously open #6320 component-traversal contribution has merged.

At this snapshot, #6396 and #6486 remain open. #6396 is labeled `awaiting-author`
and has a round-4 API-design block; #6486 is labeled `ci-failed` with a failing
`sandboxed-build` check. #6524, #6530 and #6531 are closed without merging; #6524
and #6531 have `roadmap/none` labels and failed sandboxed builds, while #6530
closed with a scope block. #6528 merged and has a complete green exact-head board.
Labels and exact-head check-run summaries are available in PR details and the
supporting table. They are separate from review health: incomplete or stale
current-head evidence remains unscored. Scores retain observed earlier-round
penalties after a PR merges; they do not assert current CI or mathematical
correctness.

## Data and updates

- `data/roadmap.json`: pinned roadmap sources, milestone scope, dependencies,
  diagram layout, route trees, frontiers, summit criteria and checkpoints. Update these editorial interpretations
  when a new contribution changes the available API or next handoff.
- `data/selection.json`: explicit PR-to-milestone mapping and worked/reviewed
  attribution. A reviewed marker requires a public evidence link. Authorship
  alone never establishes review attribution.
- `data/prs.json`: public metadata and preserved review observations for exactly
  the selected PRs. The collector stores no comment bodies or credentials.
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

Discovery reports unmapped authored GeometricTopology PRs without adding them.
Reviewed-only PRs require an explicit entry supported by review evidence. Refresh
updates new/open PRs and preserves terminal records; use `--all` to refresh every
selected PR. A failed request leaves the previous snapshot intact. Successive
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
selected PRs, plotted at local noon (the day plus its two adjacent days). Unassessed points have a separate lane.

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
`TauCetiProject/TauCeti` commit `cb3a8b39d615e65c4b1168118126b167073d745b`.
The 13 September refresh verified that the pinned roadmap text is unchanged
at roadmap head `d347d0841aa36be073aebcc678a7b6bb0d4b5188`. The Whitney
coordinate milestone includes global-chart topology, manifold-source
vector-valued jets and normed-space smooth-family continuity. General target
charts and the general manifold map into `Diff(M)` remain separate open milestones.
The global-chart Diff contribution is a separate milestone under review. Global
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
