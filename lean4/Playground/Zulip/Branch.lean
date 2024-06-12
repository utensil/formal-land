import Lean
import Mathlib.Tactic

open Lean Meta Elab Command Tactic

/-!
  Inspired by

  - [`Lean.Elab.Tactic.focus`](https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/Basic.html#Lean.Elab.Tactic.focus)
  - [`Branch` in lean4game](https://github.com/leanprover-community/lean4game/blob/main/server/GameServer/Commands.lean), see also [its doc](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#proof)
  - [`tada` on Zulip`](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Lean.203.20or.204.3F/near/394490716)
  - [Lean auto grader](https://github.com/adamtopaz/lean_grader)
-/

elab "proofs " n:num : tactic => do
  withMainContext do
    let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
    setGoals $ List.replicate (n.raw.toNat) mvarId ++ mvarIds

elab (name := proof) "proof" _n:(num)? _desc:interpolatedStr(term)? ":" t:tacticSeq : tactic => do
  withMainContext do
    let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved

    -- focus on the first goal
    setGoals [mvarId]
    -- save the non-proven state for recover after the proof
    let b ← saveState

    -- run the proof
    let a ← evalTactic t

    -- detect sorry in proof
    if let some proof := (← getMCtx).eAssignment.find? mvarId then
      if proof.isSorry then
        logWarning "proof uses 'sorry'"

    -- detect unsolved goals
    let gs ← getUnsolvedGoals
    if !gs.isEmpty then
      Term.reportUnsolvedGoals gs

    -- if it's not the last alternative proof, restore the non-proven state and restore the remaining goals
    -- otherwise the remaining goal will be proven automatically
    if !mvarIds.isEmpty then
      let msgs ← Core.getMessageLog
      b.restore
      setGoals mvarIds
      Core.setMessageLog msgs
    -- else use the last proof as the proof
    -- TODO this doesn't guarantee that the whole theorem is proven if any of the proofs are valid
    -- it also doesn't guarantee that the whole theorem is proven only if all of the proofs are valid

    pure a

elab (name := QED) "QED" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logInfo " 🎉 Goals accomplished"
  else
    logError "☝️ Unresolved goals"

elab (name := WIP) "WIP" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logError " 🎉 Goals accomplished, mark it with QED"
  else
    logWarning "☝️ Unresolved goals"

example (a b c : ℕ) : a + b * c = c * b + a := by
  proofs 2
  proof 1:
    rw [Nat.add_comm, @Nat.add_right_cancel_iff, Nat.mul_comm]
  proof 2:
    ring

-- to see the colorful effect, comment out #guard_msgs in
/--
warning: proof uses 'sorry'
---
error: unsolved goals
⊢ 2 + 1 = 3
-/
#guard_msgs in
theorem ex : 1 + 2 = 3 := by
  proofs 5
  proof "trivial":
    rfl
  proof "automatic":
    simp
  proof "cheating":
    sorry
  proof "WIP":
    rewrite [Nat.add_comm]
  proof "verbose":
    have h : 1 + 2 = 3 := by rfl
    exact h


example : 1 + 1 = 2 := by
  proofs 2
  proof 1:
    rfl
  proof 2:
    linarith
  QED
