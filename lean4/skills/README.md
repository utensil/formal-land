# ut-lean skills

Installable Lean and mathlib skills for formalization practice. Each skill is a
directory with a `SKILL.md` entry point (YAML frontmatter plus procedure) and,
where useful, one reference file.

## The skills

| Skill | Owns | References |
| --- | --- | --- |
| `ut-lean-recon` | the pinned-revision survey, no-gap manifests, evidence levels | consumed by design, golf, review |
| `ut-lean-design` | the five-question compact design check, convention locks, the authoritative-spec principle, the characteristic-API rules, the work-unit boundary | slice selection from ut-lean-roadmap; recon verdicts from ut-lean-recon |
| `ut-lean-golf` | interface-first golf, the mathlib-history escalation triggers, the post-golf boundary recheck | the pinned-source survey from ut-lean-recon |
| `ut-lean-review` | Lean-specific review checks, the contest protocol; references the TauCeti rubrics | rubrics from TauCetiProject/TauCetiReview; design rules from ut-lean-design |
| `ut-lean-ops` | toolchain-level setup, cache, audits, the verification chain, float honesty | check for independent-kernel verification |
| `ut-lean-check` | the comparator / nanoda harness, native-execution oracles | ops for toolchain-level verification |
| `ut-lean-roadmap` | the definitions (layer, slice, route, work unit), slice-selection gates, the operational algorithm, route dynamics | design for per-unit design; recon for unit selection support |

## Deduplication rule

A concept is owned by exactly one skill. When another skill needs it, it
references the owner by name and does not restate the content. The ownership
map above is the authority:

- The pinned-source survey belongs to `ut-lean-recon`; golf and design point to it.
- Slice selection (the gate table and the operational algorithm) belongs to
  `ut-lean-roadmap`; design scores candidates there rather than restating the gates.
- The characteristic-API rules belong to `ut-lean-design`; review checks them and references design.
- The TauCeti rubrics are linked, never restated, in `ut-lean-review`.
- Cross-cutting cautions (re-verify pinned examples before treating a skill as stable, public prose discipline) are one-line reminders, not sections.

## Vocabulary

The primary unit of work across these skills is the work unit: the concrete
deliverable of one step in a route, which may naturally map to a pull request
where a project uses them. See `ut-lean-roadmap` for the definitions of
roadmap, layer, slice, route, and work unit.

## Workflow

Skills are polished on the `dev/lean-skills` branch and merged to `main` from
time to time. Before a skill is treated as stable, re-verify its pinned
mathlib examples against the current pinned revision (API names drift).
