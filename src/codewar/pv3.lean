import tactic.suggest
import tactic.basic

def sum_simple (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| n@(m+1) := f n + sum_simple m

def sum_aux : ℕ → (ℕ → ℕ) → ℕ → ℕ
| a f 0       := f 0 + a
| a f n@(m+1) := sum_aux (f n + a) f m

def sum_tail := sum_aux 0

-- def sum_tail₂ : (ℕ → ℕ) → ℕ → ℕ
-- | f 0       := f 0
-- | f n@(m+1) := sum_aux (f n) f m

def idf (x : ℕ) : ℕ := x

#reduce sum_simple idf 4

#print notation @

-- lemma sum_aux_eq (a f n) :
-- sum_aux a f n = a + sum_aux 0 f n :=
-- begin
-- induction n,
-- case nat.zero {
--     rw sum_aux,
--     rw sum_aux,
--     simp,
--     apply add_comm
-- },
-- case nat.succ : m ih {
    
--     -- simp [ih],

--     sorry
-- }
-- -- induction a,
-- -- case nat.zero {
-- --     simp
-- -- },
-- -- case nat.succ : b ib {
-- --     apply eq.symm,
-- --     rw nat.succ_add,
-- --     rw <-ib,
    
-- -- }
-- end

theorem sum_eq (f n) : sum_tail f n = sum_simple f n :=
begin
induction n,
case nat.zero {
    refl
},
case nat.succ : m ih {
    rw sum_simple,

    -- apply eq.symm, -- f (m + 1) + sum_simple f m = sum_tail f (nat.succ m)
    -- rw <- ih,
    -- rw sum_tail,
    -- apply eq.symm, -- sum_aux 0 f (nat.succ m) = f (m + 1) + sum_aux 0 f m
    -- rw sum_aux,
    -- rw add_zero, -- sum_aux (f (m + 1)) f m = f (m + 1) + sum_aux 0 f m
    -- simp only [add_zero], --squeez_simp
    
    conv_rhs {
        rw <- ih,
    },
    rw sum_tail,
    rw sum_aux,
    rw add_zero,

    --tidy?,

    -- trace_simp_set,
    
    -- suggest
    -- hint
    -- library_search
    -- rw <- sum_tail,
    -- rw ih,
    -- rw <- sum_simple,
    -- conv {
    --     to_rhs,
    --     congr,
    --     skip,
        
    -- },

    -- simp [sum_simple, sum_tail, ih, sum_aux],
    -- -- rw sum_simple,
    -- -- apply eq.symm,
    -- -- rw <- ih,
    -- -- rw sum_tail,
    -- -- simp [sum_aux],
    -- -- apply eq.symm,
    

    -- rw sum_tail,
    -- rw sum_aux,
    -- simp,
    -- rw sum_simple,
    
    -- rw sum_aux,
    -- simp,
    -- rw add_comm,
    -- apply eq.symm,
    

    sorry
    -- rw <- sum_aux_eq,
}
end
-- | f 0 := sorry
-- | f n@(m+1) := sorry