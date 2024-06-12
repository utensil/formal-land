-- import Mathlib
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Control.Traversable.Basic
import ImportGraph.Imports

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Agda.20style.20interactive.20case.20splitting.3F/near/424179379
-- def foo (n : Nat) : Nat := by
--   induction n with
-- Cmd+. => Code action: generate an explicit pattern match for 'induction'
def foo (n : ℕ) : ℕ := by
  induction n with
  | zero => sorry
  | succ n ih => sorry


-- https://github.com/leanprover-community/batteries/pull/577
-- instance : Monad Id := _
-- Cmd+. => Code action: Generate a (maximal) skeleton for the structure under construction
instance : Monad Id where
  pure := sorry
  bind := sorry

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60.23minimize_imports.60.20doesn't.20find.20notation.20imports
#minimize_imports

#find_home Nat

#check ℕ

-- To use `shake`:
-- lake build Playground.Zulip.CodeAction
-- lake exe shake Playground.Zulip.CodeAction
