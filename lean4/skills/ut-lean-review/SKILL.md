---
name: ut-lean-review
description: 'Review Lean formalizations against the live Tau Ceti rubrics plus three compact evidence checks: prerequisite state, public consumer contracts, and aggregate helper/import reuse.'
---

# ut-lean-review

## Procedure

1. Refresh TauCetiReview and read `rubrics/_common.md` plus every current
   angle file in `rubrics/`. All are required.
2. Bind the review to the exact base and aggregate diff. Any source change
   invalidates it.
3. Run the three additional rubrics in [RUBRICS.md](RUBRICS.md). Record the
   requested artifact, not a general assurance.
4. Write the scoreboard under `~/tmp/` until project archival, never `/tmp/`.
   Record one row per Tau Ceti and additional rubric:

   ```md
   - Reviewed: YYYY-MM-DD
   - Subject: exact candidate
   - Base: commit
   - Head: commit or content hash
   - Reviewer: independent agent

   | rubric id | verdict | evidence | comment |
   |---|---|---|---|
   | `correctness` | `approve` | concrete inspection or probe | rubric-specific conclusion |
   ```

   Use `approve`, `request_changes`, or `block`. Keep evidence concrete and
   comments short.
5. Validate the scoreboard against the live Tau Ceti rubric directory:

   ```bash
   python3 scripts/validate-review-evidence.py REVIEW.md /path/to/TauCetiReview/rubrics
   ```

   `FORMAT/BINDING PASS` means the required metadata and rubric rows are
   present and marked green; it does not validate the reviewer's judgment. A
   negative review is complete but fails the private gate until its findings
   are resolved.

## Rules

- Review the complete aggregate diff. Inventory every added or changed
  declaration before judging the headline result.
- Verify claims with source inspection, searches, deletion or consumer probes,
  and Lean output. Never mark an unperformed check `approve`.
- A finding that changes hypotheses, public API, construction, or ownership
  invalidates dependent approvals. Return to recon/design, then review the full
  aggregate and reconcile every earlier finding before approval.
