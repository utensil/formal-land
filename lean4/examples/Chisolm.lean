import Mathlib
import Mathlib.Data.Matrix.Notation

variable {ι : Type _} {R : Type _} {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

variable [Invertible (2 : R)]

#check CliffordAlgebra

-- local notation "𝒢" => CliffordAlgebra

variable (_u _v _w : M)

#check CliffordAlgebra.ι Q _u

-- def u : CliffordAlgebra Q := CliffordAlgebra.ι Q _u

-- def v : CliffordAlgebra Q := CliffordAlgebra.ι Q _v

-- def w : CliffordAlgebra Q := CliffordAlgebra.ι Q _w

variable (u v w : CliffordAlgebra Q)

variable (u v w : CliffordAlgebra Q)

def half : CliffordAlgebra Q := algebraMap R _ ⅟2

#check u

example : 1 + 1 = 2 := by
  rfl

-- example : u * v = u * v := by
--   done

-- local notation "𝟙" => (algebraMap R _ 1 : CliffordAlgebra Q)
-- local notation "𝟚" => (algebraMap R _ 2 : CliffordAlgebra Q)

-- def 𝟙 := algebraMap R _ 1

-- example : 𝟚 * ⅟ 𝟚 = 𝟙 := by
  
--   done

lemma half_mul_two_eq_one' : ⅟2 * 2 = (1 : R) := by
  rw [invOf_mul_self']
  done

lemma one_eq_map_one : (1 : CliffordAlgebra Q) = algebraMap R _ 1 := by
  simp only [map_one]
  done

lemma two_eq_map_two : (2 : CliffordAlgebra Q) = algebraMap R _ 2 := by
  simp only [map_ofNat]
  done

local notation "𝒢" => algebraMap R (CliffordAlgebra Q)

lemma mul_eq_mul {a b : R} : 𝒢 (a * b) = 𝒢 a * 𝒢 b := by
  simp only [map_mul]
  done

lemma half_mul_two_eq_one : half * 2 = (1 : CliffordAlgebra Q) := by
  rw [one_eq_map_one]
  rw [two_eq_map_two]
  unfold half
  rw [←mul_eq_mul]
  rw [←half_mul_two_eq_one']
  done

-- lemma half_mul_two_eq_one'' : half * (2 : CliffordAlgebra Q) = algebraMap R _ (⅟2 * 2) := by
--   simp only [invOf_mul_self', map_one, half_mul_two_eq_one]
--   done

lemma two_mul_eq_add_sub : 2 * (u * v) = (u * v + v * u) + (u * v - v * u) := by
    rw [add_add_sub_cancel, @two_mul]
    done

lemma mul_eq_half_add_sub : u * v = half * ((u * v + v * u) + (u * v - v * u)) := by
  rw [← two_mul_eq_add_sub]
  rw [←@mul_assoc]
  rw [half_mul_two_eq_one]
  rw [one_mul]
  done

lemma mul_eq_half_add_half_sub : u * v = half * (u * v + v * u) + half * (u * v - v * u) := by
  conv_lhs => rw [mul_eq_half_add_sub]
  rw [mul_add]
  done

  -- simp only [add_add_sub_cancel, smul_add, nsmul_eq_mul]

  -- rw [← two_mul_eq_add_sub]
  -- rw [mul_assoc, mul_assoc]
  -- rw [mul_comm (2 : R), mul_comm (2 : R)]
  -- rw [mul_inv_of_self, one_mul, one_mul]
  -- done

-- example : u * v = half * (u * v + v * u) + half * (u * v - v * u) := by
--   calc
--     2 * (u * v) = (u * v + v * u) + (u * v - v * u) := by rw [add_add_sub_cancel, @two_mul]
--               _ = (u * v + v * u) + (u * v - v * u) := by rw [add_add_sub_cancel, @two_mul]

  -- have h1 : 2 * (u * v) = (u * v + v * u) + (u * v - v * u) := by
  --   rw [add_add_sub_cancel]
  --   done
  -- have h2 : 2 * u * v = (u * v + v * u) + (u * v - v * u) := by
  --   simp
  --   done

--   done

-- local macro_rules
-- | `($x ^ $y) => `(HPow.hPow $x $y)

-- #check 𝒢^n

-- syntax (name := cliffordNotation) "𝒢[" term "]" : term

#check CliffordAlgebra

#check CliffordAlgebra.gradedAlgebra

-- local notation "𝒢" => CliffordAlgebra

-- local macro_rules
-- | `($x ^ $y) => `(HPow.hPow $x $y)

-- -- #check 𝒢^n

-- -- syntax (name := cliffordNotation) "𝒢[" term "]" : term

-- namespace GradedAlgebra

-- local notation g "⟦" r "⟧'" => GradedAlgebra.proj g r

-- -- #check GradedAlgebra.proj G.ι G 0

-- -- #check G⟦0⟧

-- end GradedAlgebra



