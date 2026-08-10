---
name: ut-lean-golf
description: Structural Lean proof golf. Replaces locally rebuilt machinery with pinned library abstractions while preserving the intended public contract, imports, hypotheses, and simplification behavior.
---

# ut-lean-golf

Golf removes local machinery when the library or project already names the
same mathematics. It optimizes abstraction and elaboration cost, not line
count alone. Keep concrete calculations that expose the mathematical content.

## Use it

- when a proof rebuilds a standard map, quotient, equivalence, or decomposition;
- when a helper, proof shape, or calculation appears twice;
- when a statement is specialized although its proof is uniform;
- when review reports reuse, import, or structural-proof duplication.

## Procedure

1. **Name the object.** Identify what the proof constructs, then use
   `ut-lean-recon` to search the pinned revision by structure before changing
   tactics.
2. **Inventory the aggregate diff.** List every public or private mathematical
   helper, thin specialization, repeated calculation, and direct import. For
   every listed item, record an exact-conclusion search or
   deletion/replacement probe.
3. **Use the natural boundary.** Prefer the existing bundled construction.
   State uniform results at natural generality. Extract a shared criterion on
   its second use and place it at the earliest project-permitted owner. This
   skill never authorizes an upstream pull request.
4. **Recheck the contract.** Rebuild the affected modules and named consumers.
   Confirm hypotheses, public equations, opacity, simplification behavior,
   imports, and downstream availability. A deletion probe must compile before
   a wrapper or import is removed.
5. **Check cost when relevant.** Replace expensive search tactics only when a
   direct term or targeted lemma expresses the same mathematics. Confirm with
   `set_option profiler true` or `count_heartbeats` when cost motivates the
   change.

A golf pass may conclude with no source change. Record the aggregate inventory
and probe results either way. See `REFERENCE.md` for history-escalation
triggers and boundary examples.

## References

- Pinned-source survey and evidence: `ut-lean-recon`
- Public-contract owner: `ut-lean-design`
- Review gate: `ut-lean-review`
- Detailed triggers and rechecks: `REFERENCE.md`
