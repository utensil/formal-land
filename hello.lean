set_option trace.cc true
set_option trace.debug.dsimplify true
set_option trace.simplify.context true
set_option trace.simplify.rewrite true
-- set_option trace.debug.eqn_compiler true
-- set_option trace.debug true

-- Adapted from the default code 
-- on https://leanprover.github.io/live/latest/

lemma ℕ_addition_commutative
(n m : ℕ) : 
    n + m = m + n :=
by apply add_comm
-- by cc
-- by simp [add_comm]
-- why `simp` failed? See:
-- - https://github.com/leanprover-community/lean/blob/master/doc/changes.md#v360c-26-feb-2020
-- - https://github.com/leanprover-community/lean/pull/65

-- example is just a nameless lemma
example (n m : ℕ) : 
    n * m = m * n :=
by apply mul_comm

-- The following are adapted from 
-- Chapter 1, The Hitchhiker’s Guide to Logical Verification

-- 1.1.2 Terms

lemma function_currying_right_associative
(σ τ ν : Type) : 
    ( σ → τ → ν ) = ( σ → (τ → ν) ) :=
by reflexivity

lemma application_left_associative
(σ τ ν : Type) (t : σ → τ → ν) (u : σ) (v : τ) :
    ( t u v ) = ( (t u) v ) :=
by reflexivity

lemma lambda_right_associative
(σ τ ν : Type) (t : ν) :
    ( λx : σ, λy : τ, t ) = ( λx : σ, (λy : τ, t) ) :=
by reflexivity

lemma lambda_grouping
(σ τ ν : Type) (t : ν) :
    ( λ(x : σ)(y : τ), t ) = ( λx : σ, λy : τ, t ) :=
by reflexivity

lemma lambda_type_grouping
(σ τ ν : Type) (t : ν) :
    ( λ(x y : σ), t ) = ( λ(x : σ)(y : σ), t ) :=
by reflexivity

constants a b : ℤ
constant f : ℤ → ℤ
constant g : ℤ → ℤ → ℤ

#check a
#check f

#check λx : ℤ, g (f (g a x)) (g x b)
#check λx, g (f (g a x)) (g x b)

constant trool : Type
constants trool.true trool.false trool.maybe : trool

#check trool.maybe

-- 1.2.1 Natural Numbers

inductive ℕat : Type
| zero : ℕat
| succ : ℕat → ℕat

#print ℕat

-- 1.2.2 Arithmetic Expressions & 1.3 Function Definitions

inductive ArithmeticExpr : Type
| num : ℤ → ArithmeticExpr
| sym : string -> ArithmeticExpr
| add : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr
| sub : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr
| mul : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr
| div : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr

def eval (env : string → ℤ) : ArithmeticExpr → ℤ
| (ArithmeticExpr.num i) := i
| (ArithmeticExpr.sym s) := env s
| (ArithmeticExpr.add e₁ e₂) := eval e₁ + eval e₂
| (ArithmeticExpr.sub e₁ e₂) := eval e₁ - eval e₂
| (ArithmeticExpr.mul e₁ e₂) := eval e₁ * eval e₂
| (ArithmeticExpr.div e₁ e₂) := eval e₁ / eval e₂

def example_env₂ (key : string) : ℤ
:= if key = "any" then 100 else string.to_nat key

def example_env : string → ℤ
| "one" := 1
| "two" := 2
| "three" := 3
| "four" := 4
| "any" := 100
| key := string.to_nat key

def example_eval : ℤ
:= (eval example_env) (ArithmeticExpr.sub
    (ArithmeticExpr.div
        (ArithmeticExpr.add
            (ArithmeticExpr.sym "any") (ArithmeticExpr.num 3)
        )
        (ArithmeticExpr.num 3)
    )
    (ArithmeticExpr.mul
        (ArithmeticExpr.num 5) (ArithmeticExpr.sym "four")
    )
)
def expected_eval : ℤ
:= (100 + 3) / 3 - 5 * 4

lemma fourteen :
    example_eval = expected_eval ∧ example_eval = 14 :=
begin
apply and.intro,
refl, -- example_eval = expected_eval
refl -- example_eval = 14
end

-- 1.2.5 Lists

inductive List (α : Type) : Type
| nil : List
| cons : α → List → List

#check List.nil
#check List.cons
#check @List.nil
#check @List.cons

#check []
#check λ(α : Type) (x : α) (xs : list α), x :: xs
#check λ(α : Type) (x_1 x_ooo x_n : α), x_1 :: x_ooo :: x_n :: []

#check []
#check λ(Animal : Type) (cat : Animal) (cats : list Animal), 
    cat :: cats
#check λ(Animal : Type) (cat_1 cat_ooo cat_n : Animal), 
    cat_1 :: cat_ooo :: cat_n :: []

-- 1.3 Function Definitions

def add : ℕ → ℕ → ℕ
| m nat.zero := m
| m (nat.succ n) := nat.succ (add m n)

-- #eval employs an optimized interpreter
#eval add 2 7
-- #reduce uses Lean’s inference kernel, which is less efficient
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
| _ nat.zero := nat.zero
| m (nat.succ n) := add m (mul m n)

#eval mul 2 7

def power : ℕ → ℕ → ℕ
| _ nat.zero := 1
| m (nat.succ n) := mul m (power m n)

#eval power 2 3

def power₂ (m : ℕ) : ℕ → ℕ
| nat.zero := 1
| (nat.succ n) := mul m (power m n)

#eval power₂ 2 3

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
| nat.zero := z
| (nat.succ n) := f (iter n)

def power₃ (m n : ℕ) : ℕ
:= iter ℕ 1 (λl, m * l) n

def list_append (α : Type) : list α → list α → list α
| list.nil xs := xs
| (list.cons x xs) ys := list.cons x (list_append xs ys)

#check list_append

#eval list_append _ [3, 1] [4, 1, 5]

def list_append₂ {α : Type} : list α → list α → list α
| list.nil xs := xs
| (list.cons x xs) ys := list.cons x (list_append₂ xs ys)

#check list_append₂
#eval list_append₂ [3, 1] [4, 1, 5]

-- The at sign (@) can be used to make the implicit arguments explicit
#check @list_append₂
#eval @list_append₂ ℤ [3, 1] [4, 1, 5]
#eval @list_append₂ _ [3, 1] [4, 1, 5]

-- We can use syntactic sugar in the definition, both in the patterns
-- on the left-hand sides of := and in the right-hand sides
def list_append₃ {α : Type} : list α → list α → list α
| [] xs := xs
| (x :: xs) ys := x :: (list_append₃ xs ys)

def reverse {α : Type} : list α → list α
| [] := []
| (x :: xs) := (reverse xs) ++ [x]

-- 1.4 Lemma Statements

lemma add_commutative (m n : ℕ) :
    add m n = add n m :=
sorry

lemma add_associative (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
sorry
 
lemma mul_commutative (m n : ℕ) :
    mul m n = mul n m :=
sorry

lemma mul_add_distributive (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
sorry

lemma reverse_reverse {α : Type} (xs : list α) :
    reverse (reverse xs) = xs :=
sorry

axiom a_less_b :
    a < b
