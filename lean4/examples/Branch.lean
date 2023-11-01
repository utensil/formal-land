import Lean
import Mathlib.Tactic

open Lean Meta Elab Command Tactic

/-!
  Inspired by
  
  - [Lean auto grader](https://github.com/adamtopaz/lean_grader)
  - [`Branch` in lean4game](https://github.com/leanprover-community/lean4game/blob/main/server/GameServer/Commands.lean), see also [its doc](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#proof)
  - [`tada` on Zulip`](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Lean.203.20or.204.3F/near/394490716)
-/

elab "proofs " n:num : tactic => do
  let goals ← getGoals
  let m := n.1.toNat
  let goalsDup := List.range m |>.foldl (init := []) fun acc _ => acc ++ goals
  setGoals $ goalsDup

elab (name := proof) "proof" _n:(num)? _desc:interpolatedStr(term)? ":" t:tacticSeq : tactic => do
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  setGoals [mvarId]
  let b ← saveState
  let a <- evalTactic t
  -- let gs ← getUnsolvedGoals
  -- if !gs.isEmpty then
  --   let msgs ← Core.getMessageLog
  --   logWarning "This branch leaves open goals."
  --   Core.setMessageLog msgs

  let msgs ← Core.getMessageLog
  b.restore
  setGoals mvarIds
  Core.setMessageLog msgs
  
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
    QED
  proof 2:
    ring
    QED

example : 1 + 2 = 3 := by
  proofs 5
  proof "trivial":
    rfl
    QED
  proof "automatic":
    simp
    QED
  proof "cheating":
    sorry
    QED
  proof "WIP":
    rewrite [Nat.add_comm]
    WIP
  proof "verbose":
    have h : 1 + 2 = 3 := by rfl
    exact h
    QED
  
