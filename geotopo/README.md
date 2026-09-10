# Geometric topology route map

Open [geotopo-route-map.html](geotopo-route-map.html) directly in a browser. The
page embeds its styles, scripts, graph and snapshot data; it needs no server or
network connection. Source and PR links open the corresponding public records.

The page maps the GeometricTopology roadmap's 11 layers and six editorial work
trails. It includes all 94 PRs carrying `roadmap/GeometricTopology` at collection
on 10 September 2026: 83 merged, 8 closed without merging, and 3 open. Counts are
historical PR activity, not mathematical completion or a list of surviving APIs.

## Evidence and interpretation

- Roadmap: `TauCetiProject/TauCetiRoadmap` at
  `d58f0b411ad04e1074ba20a69d1c5fb0c4b88da3`, under
  `TauCetiRoadmap/GeometricTopology/`. Dependency relations link to exact lines.
- Selected Lean source checks: `TauCetiProject/TauCeti` at
  `be0b30f3963c7f5158674dca96d7fe3fdd0dcd20`. The weak Whitney contribution is
  chart-level, and the contractible two-complex predicate does not prove Zeeman's
  conjecture.
- Public PR evidence: paginated GitHub PR metadata, changed files, retained
  commits, issue lifecycle events and machine-readable review-comment metadata;
  checks and commit statuses were also collected for the three open PR heads.
- TCWORK attribution covers seven verified owned PRs. TCREVIEW attribution covers
  five PRs with completed-review evidence, including one closed without merging.
  This is a verified minimum; an absent marker does not mean no review occurred.
- PR-to-layer assignments and work trails are editorial interpretations of titles
  and changed files. The cited roadmap dependencies are not Lean import edges.
- Review comments can be edited. The timeline shows observed review metadata and
  workflow events, not an immutable reconstruction of every past review state.
  Current-head review evidence is distinguished from older scoreboards.
- The generated roadmap `STATUS.md` is dated 1 September 2026. It is a historical
  baseline, not the date of this newer PR snapshot. Layers with no assigned PRs
  make no absence claim about Mathlib or other roadmaps.

The roadmap aims to make theorems faithfully stateable. This page is not a new
proof audit and does not assign a weighted completion or health score.

## Updating and publishing

Refresh the labeled PR cohort and its paginated evidence, pin the roadmap and
source revisions, review the route assignments, then replace the embedded data.
Keep the timestamps and interpretation notes with the snapshot. Verify filters,
exact-head review handling, mobile layout and direct-file offline use before
publishing an update.

Geotopo CI uploads this directory as `pages-geotopo`. The shared Pages deployment
consumes successful main-branch artifacts and publishes it under `/geotopo/`.
PR builds stage an artifact for checking and do not trigger production deployment.
