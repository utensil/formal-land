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
4. Write one internal review scoreboard row per Tau Ceti and additional rubric:

   ```md
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

   Only a validator pass satisfies the private review gate.

## Rules

- Review the complete aggregate diff. Inventory every added or changed
  declaration before judging the headline result.
- Verify claims with source inspection, searches, deletion or consumer probes,
  and Lean output. Never mark an unperformed check `approve`.
- Return architectural findings about prerequisites, hypotheses, public API,
  or module ownership to recon/design; dependent reviews become provisional.
