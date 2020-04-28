lemma ℕ_addition_commutative
(n m : ℕ) : 
n + m = m + n :=
by cc
-- TODO why simp failed?

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

inductive ℕat : Type
| zero : ℕat
| succ : ℕat → ℕat

#print ℕat

inductive ArithmeticExpr : Type
| num : ℤ → ArithmeticExpr
| sym : string -> ArithmeticExpr
| add : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr
| sub : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr
| mul : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr
| div : ArithmeticExpr → ArithmeticExpr → ArithmeticExpr

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
