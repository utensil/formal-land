import Lean
import Playground.Zulip.EnvExInit

open Lean Meta Elab Command Tactic

/--
error: unsolved goals
⊢ 1 + 2 = 3
-/
#guard_msgs in
theorem foo : 1 + 2 = 3 := by
  Proof "trivial":
    rfl
