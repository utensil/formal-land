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
  let goals ← getGoals
  let m := n.1.toNat
  let goalsDup := List.range m |>.foldl (init := []) fun acc _ => acc ++ goals
  setGoals $ goalsDup

elab (name := proof) "proof" _n:(num)? _desc:interpolatedStr(term)? ":" t:tacticSeq : tactic => do
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  setGoals [mvarId]
  let b ← saveState
  let a <- evalTactic t

  let localState : Tactic.State ← get
  -- let env <- getEnv
  -- let cs := env.constants
  -- let c := cs.find? `sorryAx |>.get!
  if let some val := (← getMCtx).eAssignment.find? mvarId then
    if val.isSorry then
      logWarning "proof uses 'sorry'"

  let gs ← getUnsolvedGoals
  if !gs.isEmpty then
    Term.reportUnsolvedGoals gs

  if !mvarIds.isEmpty then
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
  proof 2:
    ring

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
