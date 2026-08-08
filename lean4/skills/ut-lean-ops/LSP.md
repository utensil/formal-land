---
name: ut-lean-ops-lsp
description: "Optional LSP triage and semantic lookup for Lean work: pre-build diagnostics on long builds, semantic consumer discovery when text search is noisy, and goal-state support during interactive repair. Routine slice work does not need it."
---

# LSP triage and semantic lookup (optional)

A Lean language server (for example `lean-lsp-mcp` registered with the agent
harness) is optional. Routine slice work does not need it: `lake build`
diagnostics and the audits in SKILL.md are the normal flow. Use it only when
it earns its keep:

- before a long or broad full build: read the changed file's diagnostics
  first to catch obvious errors early;
- when the affected-module or consumer-probe check needs a precise consumer
  list and text search is too noisy: find-references locates them
  semantically;
- during interactive repair or golf inside a slice: goal states and hover
  information beat guesswork.

Bounds: the LSP reads the built state of a hydrated worktree, so it does not
exist in a fresh checkout and it never replaces the authoritative gates —
the cache-first build, the source audits, and fresh-checkout reproduction
remain the bar. A green editor is not a green build. (Adopted 2026-08-08
from jstoobysmith/PhyslibAITools, `Tasks/Golf.md` and sibling task prompts;
not yet verified.)
