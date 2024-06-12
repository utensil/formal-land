-- https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/Testing.20if.20tactics.20work
import Lean
import Mathlib.Tactic

theorem eg₁ : ∀ (a : Nat), Nat.succ a = Nat.zero → False := by
  intro a h; exact (Eq.mpr (congrArg (fun _a ↦ match _a with | Nat.zero => True | Nat.succ a => False) h) True.intro)

open Lean Meta Elab Term Tactic Parser.Tactic

def chkTacticSeq (type: Expr)(tacs : TSyntax ``tacticSeq):
  TermElabM Unit :=
  do
  try
    let mvar ← mkFreshExprMVar type MetavarKind.syntheticOpaque
    let _ ← Elab.runTactic mvar.mvarId! tacs (← read) (← get)
    return
  catch e =>
    throwError "Error: {e.toMessageData}"

def testEg : TermElabM Unit := do
  let type ← elabType <| ← `(∀ (a : Nat), Nat.succ a = Nat.zero → False)
  let pf ← `(tacticSeq| intro a h; exact (Eq.mpr (congrArg (fun _a ↦ match _a with | Nat.zero => True | Nat.succ a => False) h) True.intro))
  chkTacticSeq type pf

#eval withDeclName `foo testEg
