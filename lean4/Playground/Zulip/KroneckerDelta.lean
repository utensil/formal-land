-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/kronecker.20symbol
import Mathlib.Algebra.Group.Pi.Basic

variable (I : Type*) [DecidableEq I] (R : Type*) [Zero R] [One R]

def kronecker_delta (i j : I) : R := (Pi.single i 1 : _ → R) j
