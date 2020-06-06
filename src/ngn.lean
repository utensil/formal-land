@[derive decidable_eq]
inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

namespace mynat

instance : has_zero mynat := ⟨mynat.zero⟩

theorem mynat_zero_eq_zero : mynat.zero = 0 := rfl

def one : mynat := succ 0

instance : has_one mynat := ⟨mynat.one⟩

theorem one_eq_succ_zero : 1 = succ 0 := rfl

lemma zero_ne_succ (m : mynat) : (0 : mynat) ≠ succ m := λ h, by cases h

lemma succ_inj {m n : mynat} (h : succ m = succ n) : m = n := by cases h; refl

end mynat

attribute [symm] ne.symm

namespace mynat

-- definition of "addition on the natural numbers"
def add : mynat → mynat → mynat
| m 0 := m
| m (succ n) := succ (add m n)

instance : has_add mynat := ⟨mynat.add⟩

-- numerals now work
example : mynat := 37

lemma add_zero (m : mynat) : m + 0 = m := rfl

lemma add_succ (m n : mynat) : m + succ n = succ (m + n) := rfl

-- end of definition of "addition on the natural numbers"

end mynat

namespace mynat

def mul : mynat → mynat → mynat
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul mynat := ⟨mul⟩
-- notation a * b := mul a b

example : (1 : mynat) * 1 = 1 := 
begin
refl
end

lemma mul_zero (m : mynat) : m * 0 = 0 := rfl

lemma mul_succ (m n : mynat) : m * (succ n) = m * n + m := rfl

def pow : mynat → mynat → mynat
| m zero := one
| m (succ n) := pow m n * m

instance : has_pow mynat mynat := ⟨pow⟩
-- notation a ^ b := pow a b

example : (1 : mynat) ^ (1 : mynat) = 1 := 
begin
refl
end

lemma pow_zero (m : mynat) : m ^ (0 : mynat) = 1 := rfl

lemma pow_succ (m n : mynat) : m ^ (succ n) = m ^ n * m := rfl

end mynat

------------------------------------------------------------------------

namespace mynat

lemma example1 (x y z : mynat) : x + y + z = x + y + z :=
begin
refl,
end

lemma example1' (x y z : mynat) : x + y + z = x + y + z := rfl

lemma example2 (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by rw h

lemma example2' (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
begin
  rw h,
end

lemma example2'' (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
have h_two_mul : 2 * y = 2 * y, from rfl,
show 2 * y = 2 * (x + 7), from (by rw h)

lemma example3 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) :=
begin
  rw h,
end

lemma zero_add (n : mynat) : 0 + n = n :=
begin
  induction n,
  {
    rw mynat_zero_eq_zero,
    rw add_zero,
  },
  {
    rw add_succ,
    rw n_ih,
  }
end

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin
  induction c,
  {
    rw mynat_zero_eq_zero,
    rw add_zero (a + b),
    rw add_zero b,
  },
  {
    rw add_succ (a + b),
    rw add_succ b,
    rw add_succ a,
    rw c_ih,
  }
end

lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin
  induction b,
  {
    rw mynat_zero_eq_zero,
    rw add_zero a,
    rw add_zero (succ a),
  },
  {
    rw add_succ a,
    rw add_succ (succ a),
    rw b_ih,
  }
end

lemma add_comm (a b : mynat) : a + b = b + a :=
begin
  induction b,
  {
    rw mynat_zero_eq_zero,
    rw add_zero a,
    induction a,
    {
      rw mynat_zero_eq_zero,
      rw add_zero 0,
    },
    {
      rw add_succ 0,
      rw ← a_ih,
    }
  },
  {
    rw succ_add b_n,
    rw add_succ a,
    rw b_ih,
  }
end

theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin
  rw one_eq_succ_zero,
  rw add_succ n,
  rw add_zero n,
end

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
  induction c,
  {
    rw mynat_zero_eq_zero,
    rw add_zero (a + b),
    rw add_zero a,
  },
  {
    rw add_succ (a + b),
    rw add_succ a,
    rw succ_add,
    rw c_ih,
  }
end

-- The proof in tactic mode
lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin
induction m,
{
-- Q0: Why do I need this extra line compared to in http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/?world=3&level=1
  rw mynat_zero_eq_zero,
  rw mul_zero 0,
},
{
  rw mul_succ 0 m_n,
  rw add_zero (0 * m_n),
  rw m_ih,
}
end

-- The proof of a forall version of the lemma
-- ported from https://leanprover-community.github.io/mathlib_docs/core/init/data/nat/lemmas.html#nat.zero_mul
-- Q1: Why does it need an extra refl than the original proof?
lemma zero_mul_forall : ∀ (m : mynat), 0 * m = 0
| 0        := rfl
| (succ m) := begin
  rw [mul_succ, zero_mul_forall],
  refl
end

lemma zero_mul_forall_match : ∀ (m : mynat),  0 * m = 0
| zero :=
calc zero * zero
    = 0 * 0 : by rw mynat_zero_eq_zero
... = 0 : by rw mul_zero 0
| n@(succ m_n) :=
calc 0 * (succ m_n)
    = 0 * m_n + 0 : by rw mul_succ
... = 0 * m_n : by rw add_zero (0 * m_n)
... = 0 : by rw zero_mul_forall_match m_n

lemma zero_mul_forall_match_term : ∀ (m : mynat),  0 * m = 0
| zero :=
calc zero * zero
    = 0 * 0 : by rw mynat_zero_eq_zero
... = 0 : by rw mul_zero 0
| n@(succ m_n) :=
calc 0 * (succ m_n)
    = 0 * m_n + 0 : mul_succ 0 m_n
... = 0 * m_n : add_zero (0 * m_n)
... = 0 : by rw zero_mul_forall_match m_n

-- Q2: how can I refer to the lemma itself in the match proof at <marker>
lemma zero_mul_match (m : mynat) : 0 * m = 0 :=
match m with
| zero :=
calc zero * zero
    = 0 * 0 : by rw mynat_zero_eq_zero
... = 0 : by rw mul_zero 0
| n@(succ m_n) :=
calc 0 * (succ m_n)
    = 0 * m_n + 0 : by rw mul_succ
... = 0 * m_n : by rw add_zero (0 * m_n)
... = 0 : by sorry -- <marker>
end

lemma zero_mul_induction_zero : 0 * zero = 0 := rfl

lemma zero_mul_induction_m_n : ∀ (n : mynat), 0 * n = 0 → 0 * n.succ = 0 :=
λ m_n h, add_zero (0 * m_n) ▸ mul_succ 0 m_n ▸ h

-- Q3: Why `add_zero` is no longer needed?
lemma zero_mul_induction_m_n' : ∀ (n : mynat), 0 * n = 0 → 0 * n.succ = 0 :=
λ m_n h, mul_succ 0 m_n ▸ h

lemma zero_mul_rec (m : mynat) : 0 * m = 0 :=
mynat.rec_on m zero_mul_induction_zero zero_mul_induction_m_n

lemma zero_mul_rec' (m : mynat) : 0 * m = 0 :=
mynat.rec_on m rfl (λ m_n h, mul_succ 0 m_n ▸ h)

-- lemma zero_mul_rec'' (m : mynat) : 0 * m = 0 :=
-- m.rec_on zero_mul_induction_zero zero_mul_induction_m_n

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Natural.20Numbers.20Game/near/199964443

lemma mul_one (m : mynat) : m * 1 = m :=
begin
  induction m,
  {
    rw one_eq_succ_zero,
    rw mul_succ,
    rw mul_zero,
    refl
  },
  {
    rw one_eq_succ_zero,
    rw mul_succ,
    rw mul_zero,
    rw zero_add,
  }
end

lemma one_mul (m : mynat) : 1 * m = m :=
begin
  induction m,
  {
    rw mynat_zero_eq_zero,
    rw mul_zero,
  },
  {
    rw mul_succ,
    rw succ_eq_add_one,
    rw m_ih
  }
end

lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
begin
  induction b,
  {
    rw [mynat_zero_eq_zero, add_zero, mul_zero, add_zero],
  },
  {
    rw mul_succ,
    rw add_succ,
    rw mul_succ,
    rw b_ih,
    rw add_assoc,
  }
end

lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin
induction c,
{
  rw mynat_zero_eq_zero,
  rw mul_zero (a * b),
  rw mul_zero b,
  rw mul_zero a,
},
{
  rw mul_succ (a * b),
  rw mul_succ b,
  rw c_ih,
  rw mul_add a,
}
end

lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin
  induction b,
  {
    rw mynat_zero_eq_zero,
    rw mul_zero,
    rw mul_zero,
    rw add_zero,
  },
  {
    rw mul_succ,
    rw mul_succ,
    rw add_succ,
    rw add_succ,
    rw b_ih,
    rw add_assoc,
    rw add_comm b_n a,
    rw ←add_assoc,
  }
end

lemma succ_mul' (a b : mynat) : succ a * b = a * b + b :=
begin
  induction b,
  {
    rw mynat_zero_eq_zero,
    rw mul_zero,
    rw mul_zero,
    rw add_zero,
  },
  {
    rw mul_succ,
    rw mul_succ,
    rw add_succ,
    rw add_succ,
    rw b_ih,
    rw add_right_comm,
  }
end

lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=
begin
  induction t,
  {
    rw mynat_zero_eq_zero,
    rw [mul_zero, mul_zero, mul_zero, add_zero],
  },
  {
    rw [mul_succ, mul_succ, mul_succ],
    rw t_ih,
    rw add_right_comm,
    rw add_comm (b * t_n) b,
    rw ←add_assoc(a * t_n) a b,
    rw add_assoc (a * t_n + a) b (b * t_n),
  }
end

lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
  induction b,
  {
    rw mynat_zero_eq_zero,
    rw [mul_zero, zero_mul],
  },
  {
    rw [mul_succ, succ_mul, b_ih],
  }
end

lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc b a c,
  rw mul_comm b a,
  rw mul_assoc a b c
end

lemma zero_pow_zero : (0 : mynat) ^ (0 : mynat) = 1 :=
begin
  rw pow_zero,
end

lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 :=
begin
  rw [pow_succ, mul_zero],
end

lemma pow_one (a : mynat) : a ^ (1 : mynat) = a :=
by rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]

lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin
induction m with n h,
{
  rw mynat_zero_eq_zero,
  rw pow_zero,
},
{
  rw pow_succ,
  rw h,
  refl,
}
end

lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n with k h,
  {
    rw mynat_zero_eq_zero,
    rw pow_zero,
    rw add_zero,
    rw mul_one,
  },
  {
    rw add_succ,
    rw [pow_succ, pow_succ],
    rw h,
    rw mul_assoc (a ^ m) (a ^ k) a,
  }
end

lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=
begin
induction n with k h,
  {
    rw mynat_zero_eq_zero,
    rw [pow_zero, pow_zero, pow_zero],
    refl,
  },
  {
    rw [pow_succ, pow_succ, pow_succ],
    rw h,
    rw mul_assoc (a ^ k) (b ^ k) (a * b),
    rw mul_left_comm (b ^ k) a b,
    rw mul_assoc (a ^ k) a (b ^ k * b),
  }
end

lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) :=
begin
  induction n with k h,
  {
    rw mynat_zero_eq_zero,
    rw [pow_zero, mul_zero, pow_zero],
  },
  {
    rw [pow_succ, mul_succ],
    rw h,
    rw pow_add a (m * k) m,
  }
end

lemma two_eq_succ_one : 2 = succ 1 := rfl

lemma add_squared (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b :=
begin
  rw two_eq_succ_one,
  rw one_eq_succ_zero,
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ],
  rw [pow_zero, pow_zero, pow_zero],
  rw [one_mul, one_mul, one_mul],
  rw mul_add,
  rw add_mul,
  rw add_mul,
  rw mul_comm b a,
  rw succ_mul,
  rw ←one_eq_succ_zero,
  rw one_mul,
  rw add_mul,
  rw add_assoc (a * a) (a * b) (a * b + b * b),
  rw add_assoc (a * a) (b * b) (a * b + a * b),
  rw ←add_assoc  (b * b) (a * b) (a * b),
  rw add_comm  (b * b) (a * b),
  rw add_assoc (a * b) (b * b) (a * b),
  rw add_comm (b * b) (a * b),
end -- 28 rewrites

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/natural.20number.20game.20questions/near/196864644
lemma add_squared' (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b :=
begin
  rw two_eq_succ_one,
  rw pow_succ,
  rw pow_succ,
  rw pow_succ,
  rw pow_one,
  rw pow_one,
  rw pow_one,
  rw add_mul,
  rw mul_add,
  rw mul_add,
  rw succ_mul,
  rw one_mul,
  rw add_mul,
  rw mul_comm b a,
  rw add_assoc,
  rw add_assoc,
  rw add_comm (b * b),
  rw add_assoc,
end

-- Adapted from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/natural.20number.20game.20questions/near/196867894
lemma add_squared'' (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b :=
begin
  have two_mul: ∀ x : mynat, (2:mynat) * x = x + x := λx, by rw [two_eq_succ_one, succ_mul 1 x, one_mul],
  have pow_two: ∀ x : mynat, x ^ (2:mynat) = x * x := λx, by rw [two_eq_succ_one, pow_succ, pow_one],
  rw [pow_two, pow_two, pow_two],
  rw [add_mul, two_mul, add_right_comm, add_mul],
  rw [← add_assoc, ← mul_add, mul_add b, mul_comm b, add_assoc]
end

/-

Dark mode for http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/:

body, button, .accordion__button,.accordion__panel {
    background-color: #202020 !important;
    color: #cdcdcd;

}

.Resizer {
    background-color: #535353 !important;
}

/*
Press F12, choose Console, copy-paste the following and hit Enter:

monaco.editor.setTheme('vs-dark');
*/

-/

end mynat