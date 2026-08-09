# Review rubric registry

This is the required-id registry for `ut-lean-review`. Refresh the Tau Ceti
rows from the latest `TauCetiReview/rubrics/` before a review if that repository
adds or removes an angle. Do not rename an extension id without migrating
stored review evidence.

| rubric id | source | review angle |
|---|---|---|
| `correctness` | TauCetiReview | Statements and definitions say what they should. |
| `reuse` | TauCetiReview | Existing Mathlib and project APIs are reused. |
| `scope` | TauCetiReview | The change is on-roadmap and one coherent topic. |
| `attribution` | TauCetiReview | Formal and informal sources are credited. |
| `api-design` | TauCetiReview | The public surface is minimal and characteristic. |
| `generality` | TauCetiReview | Assumptions and abstraction level are natural. |
| `placement` | TauCetiReview | Declarations and imports have the canonical owner. |
| `naming` | TauCetiReview | Names describe conclusions and follow conventions. |
| `documentation` | TauCetiReview | Module and declaration documentation is accurate. |
| `proof-quality` | TauCetiReview | Proofs are robust, explicit at boundaries, and maintainable. |
| `ut-review-head-binding` | ut-lean-review | Bind the verdict to the exact aggregate diff and head. |
| `ut-review-revision` | ut-lean-review | Recheck the full affected surface after material revisions. |
| `ut-review-contest` | ut-lean-review | Reconcile interacting or contested findings with evidence. |
| `ut-reuse-search-before-writing` | ut-lean-review | Confirm structural reuse was searched before authoring. |
| `ut-generality-uniformity` | ut-lean-review | Probe whether apparently fixed arguments are uniform. |
| `ut-proof-robustness` | ut-lean-review | Perturb implementation boundaries and reject brittle proofs. |
| `ut-documentation-dependency-claims` | ut-lean-review | Detect documentation that hides selected data or assumptions. |
| `ut-naming-future-models` | ut-lean-review | Test names against known successor models and equivalences. |
| `ut-placement-import-probes` | ut-lean-review | Decide ownership and imports with compile probes. |
| `ut-structural-boundaries` | ut-lean-review | Review stack, module, root, and aggregator boundaries. |
