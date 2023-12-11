-- -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Mechanics.20of.20Proof.201.2E3.2E11.20exercise.2015
import Mathlib

-- -- https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id29
example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
    y = 0 / x + y := by ring
    _ = (2 * x - y * x) / x + y := by rw [h2]
    _ = ((2 - y) * (x + 3 - 3)) / x + y := by ring
    _ = ((2 - y) * (5 - 3)) / x + y := by rw [h1]
    _ = (2 - y) * 2 / x + y := by ring
    _ = (2 - y) * 2 / (x + 3 - 3) + y := by ring
    _ = (2 - y) * 2 / (5 - 3) + y := by rw [h1]
    _ = (2 - y) + y := by ring
    _ = 2 := by ring

example : 6 = 3 + 3 := by
  have h : 6 = 2 + 4 := by
    calc
      6 = 1 + 5 := by rw [Nat.one_add]
      _ = 2 + 4 := by rw [@Nat.add_right_cancel_iff]
      _ = 3 + 3 := by rw [@Nat.add_right_cancel_iff]
  exact h
  done
