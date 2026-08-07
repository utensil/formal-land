# ut-lean skills

Installable Lean and mathlib skills for formalization practice. Each skill is a
directory with a `SKILL.md` entry point (YAML frontmatter plus procedure) and,
where useful, one reference file.

## The skills

| Skill | Owns | References |
| --- | --- | --- |
| `ut-lean-recon` | the pinned-revision survey, no-gap manifests, evidence levels | consumed by design, golf, review |
| `ut-lean-design` | the five-question compact design check, convention locks, the authoritative-spec principle, the characteristic-API rules, the slice boundary | slice selection from ut-lean-roadmap; recon verdicts from ut-lean-recon |
| `ut-lean-golf` | interface-first golf, the mathlib-history escalation triggers, the post-golf boundary recheck | the pinned-source survey from ut-lean-recon |
| `ut-lean-review` | Lean-specific review checks, the contest protocol; references the TauCeti rubrics | rubrics from TauCetiProject/TauCetiReview; design rules from ut-lean-design |
| `ut-lean-ops` | toolchain-level setup, cache, audits, fresh-checkout reproduction; the executable verification chain (VERIFY.md) is a scoped extension gated on the project carrying executable content | check for independent-kernel verification |
| `ut-lean-check` | the comparator / nanoda harness, native-execution oracles | ops for toolchain-level verification |
| `ut-lean-roadmap` | the definitions (roadmap, layer, route, slice), slice-selection gates, the operational algorithm, route dynamics | design for per-slice design; recon for slice selection support |

## Interfaces

Reconnaissance runs before design, and golf and review consume its verdict.
The relationship is sequential with iterative refinement: design may re-invoke
recon in focused form (a compile probe against the pinned revision) when its
convention locks or signature choices raise new API questions, and the two
converge when the design's contracts are pinned against recon evidence.

## Deduplication rule

A concept is owned by exactly one skill. When another skill needs it, it
references the owner by name and does not restate the content. The ownership
map above is the authority:

- The pinned-source survey belongs to `ut-lean-recon`; golf and design point to it.
- Slice selection (the gate table and the operational algorithm) belongs to
  `ut-lean-roadmap`; design scores candidates there rather than restating the gates.
- The characteristic-API rules belong to `ut-lean-design`; review checks them and references design.
- The TauCeti rubrics are linked, never restated, in `ut-lean-review`.
- Cross-cutting cautions (re-verify pinned examples before treating a skill as stable, public prose discipline, example citations carry their spirit inline (a bare reference an agent cannot explore is rewritten or dropped)) are one-line reminders, not sections.

## Term ownership

Definitions of the four terms live in exactly one place, `ut-lean-roadmap`
(the deduplication rule); the slice is the term that flows through the other
skills because it is the unit of work.

| Term | Defined in | Concept owned by | Consumed by |
| --- | --- | --- | --- |
| roadmap | ut-lean-roadmap | ut-lean-roadmap (reading the layers, spine, frontier; acceptance oracles; roadmaps as human intent) | design and recon as context |
| layer | ut-lean-roadmap | ut-lean-roadmap (logical dependency structure) | roadmap only |
| route | ut-lean-roadmap | ut-lean-roadmap (picking the route, the attack angle and plan, navigation, route dynamics) | roadmap only, as a term |
| slice | ut-lean-roadmap | selection and scoping in ut-lean-roadmap (a function of that skill, not a separate one); design in ut-lean-design; reconnaissance in ut-lean-recon; delivery in ut-lean-golf; review in ut-lean-review | every skill that works on a contribution |

Per skill, the slice appears as: selected and scoped in ut-lean-roadmap,
designed in ut-lean-design, supported by reconnaissance in ut-lean-recon,
delivered in ut-lean-golf, and reviewed in ut-lean-review. ut-lean-ops and
ut-lean-check are orthogonal to the terms: they verify and check the work
rather than slice it.

## Vocabulary

The primary unit of work across these skills is the slice: the selected next
slice of work, which naturally maps to a pull request where a project uses
them. The route is picked through the roadmap and carries the attack angle and
the practical plan. See `ut-lean-roadmap` for the definitions of roadmap,
layer, route, and slice.

## Workflow

Skills are polished on the `dev/lean-skills` branch and merged to `main` from
time to time. Before a skill is treated as stable, re-verify its pinned
mathlib examples against the current pinned revision (API names drift).
