import Lean
import Playground.Zulip.EnvExInit

open Lean Meta Elab Command Tactic

/--
error: unsolved goals
⊢ 1 + 2 = 3
-/
-- v4.32: running `Proof` in an async context now emits a `mainOnly`-extension panic as an
-- `info` message with a platform-dependent backtrace; drop info messages, keep checking errors.
#guard_msgs (drop info, check error) in
theorem foo : 1 + 2 = 3 := by
  Proof "trivial":
    rfl
