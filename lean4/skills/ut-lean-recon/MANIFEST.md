# Recon Manifest Template

Attach this manifest to every recon verdict. Fill one row per requirement and label every claim by evidence level: `compiled`, `spike-boundary`, `inspected API`, or `proposed`.

## Verdict

| Field | Value |
| --- | --- |
| Target statement | |
| Pinned mathlib commit | |
| Lean toolchain | |
| Project commit | |
| Pinned checkout path | |
| Verdict | direct / no-gap / blocker |
| Verdict summary | |

## Source-role versus existing declaration

| Source role | Existing declaration | What is already formalized | Evidence |
| --- | --- | --- | --- |
| | | | |

## API reachability

| Requirement | Classification | Pinned API or missing work | Evidence |
| --- | --- | --- | --- |
| | | | |

Classification values: `direct` (suitable declaration already present), `local lemma` (buildable from present APIs without new general theory), `infrastructure blocker` (reusable construction or equivalence needed before the result can be stated honestly).

## Failed-probe journal

| Remembered (wrong) name | Failure | Correct route | Evidence |
| --- | --- | --- | --- |
| | | | |

## Convention comparison

| Item | Library side | Target side | Matched? |
| --- | --- | --- | --- |
| | | | |

For every equality claim also record, outside the table: direction of the map, source and target forms, signs, scalar factors.

## Collision search log

| Scope searched | Query | Result |
| --- | --- | --- |
| pinned mathlib | | |
| project merged history | | |
| open project pull requests | | |
| adjacent project lanes | | |

## Evidence level labels

- `compiled`: elaborated on the pinned toolchain.
- `spike-boundary`: elaborated with a named sorry boundary that states the exact obligation postponed.
- `inspected API`: read from the pinned source, not elaborated.
- `proposed`: intended, not yet checked.

## No-gap conclusion

If the verdict is `no-gap`, record here the exact boundary covered: hypotheses, direction, conventions, and why no wrapper theorem is justified. If the verdict is `blocker`, list the missing infrastructure and what a later slice must establish first.
