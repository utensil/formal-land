-- https://leanprover.github.io/theorem_proving_in_lean/

open classical

-- 1.3. About this Book

-- Structural Proof
lemma add_commutative₁ (p q : Prop) :
p ∧ q → q ∧ p :=
assume hpq : p ∧ q,
have hp : p, from and.left hpq,
have hq : q, from and.right hpq,
show q ∧ p, from and.intro hq hp

-- Tatical Proof
lemma add_commutative₂ (p q : Prop) :
p ∧ q → q ∧ p :=
begin
intro hpq,
apply and.intro,
{
    exact and.right hpq,
},
{
    exact and.left hpq
}
end

theorem add_commutative :
∀ (p q : Prop), p ∧ q → q ∧ p :=
begin
intros p q,
-- apply add_commutative₁
apply add_commutative₂
end

-- 2.1. Simple Type Theory

constant m : nat
constant n : ℕ
constant z : ℤ

#check m
#check n
#check m + n
#check m * (n + 0)
#check z * (-1)

constants b1 b2 : bool

#check b1           
#check b1 && b2
#check b1 || b2     
#check tt
#check ff
#eval tt && ff
#eval tt || ff

constant f₀ : nat → nat           
constant f₀' : nat -> nat         
constant f₀'' : ℕ → ℕ             
constant p₀ : nat × nat           
constant q₀ : prod nat nat        
constant g₀ : nat → nat → nat
constant g₀' : nat → (nat → nat)  
constant h₀ : nat × nat → nat

constant Fun : (nat → nat) → nat   -- a "functional"

#check f₀        
#check f₀ n      
#check g₀ m n    
#check g₀ m      
#check (m, n)   
#check p₀.1      
#check p₀.2      
#check (m, n).1 
#check (p₀.1, n) 
#check Fun f₀ 

-- 2.2. Types as Objects

#check nat               
#check bool              
#check nat → bool        
#check nat × bool        
#check nat → nat         
#check nat × nat → nat
#check nat → nat → nat
#check nat → (nat → nat)
#check nat → nat → bool
#check (nat → nat) → nat

#check Prop -- Type
#check Prop → Prop -- Type

constants α β γ: Type
constant F : Type → Type
constant G : Type → Type → Type

#check α        
#check F α      
#check F nat    
#check G α
#check G α β    
#check G α nat  

#check @prod
#check prod α β    
#check prod nat nat

#check list α  
#check list nat

#check Type     -- Type : Type 1
#check Type 1   -- Type 1 : Type 2
#check Type 2   -- Type 2 : Type 3
#check Type 3   -- Type 3 : Type 4
#check Type 4   -- Type 4 : Type 5

#check Sort     -- Prop : Type
#check Sort 1   -- Type : Type 1
#check Sort 2   -- Type 1 : Type 2
#check Sort 3   -- Type 2 : Type 3
#check Sort 4   -- Type 3 : Type 4

universe u
universe v

-- #check u     -- unknown identifier 'u'
#check Sort u   -- Sort u : Type u
#check Type u   -- Type u : Type (u+1)

constant instance_sort_u : Sort u

#check instance_sort_u -- instance_u : Sort u_1

constant instance_type_u : Type u

#check instance_type_u -- instance_type_u : Type u_1

constant instance_type_u₂ : Type u

#check instance_type_u₂ -- instance_type_u₂ : Type u_1

-- 2.3. Function Abstraction and Evaluation

#check fun x : nat, x + 5
#check λ x : nat, x + 5

#eval (λ x : nat, x + 5) 3 -- 8

constants α₁ α₂ : α
constants β₁ β₂: β

constant f : α → α
constant g : α → β
constant h : α → β → α
constant j : β → γ
constant p : α → α → bool

#check fun x : α, f x                      -- α → α
#check λ x : α, f x                        -- α → α
#check λ x : α, f (f x)                    -- α → α
#check λ x : α, h x β₁                     -- α → α
#check λ y : β, h α₁ y                     -- β → α
#check λ x : α, p (f (f x)) (h (f α₁) β₂)  -- α → bool
#check λ x : α, λ y : β, h (f x) y         -- α → β → α
#check λ (x : α) (y : β), h (f x) y        -- α → β → α
#check λ x y, h (f x) y                    -- α → β → α

constants (a : α) (b : β)

#check a
#check b

#check λ x : α, x        -- α → α
#check λ x : α, b        -- α → β
#check λ x : α, g (f x)  -- α → γ
#check λ x, g (f x)

#check λ b : β, λ x : α, x     -- β → α → α
#check λ (b : β) (x : α), x    -- β → α → α
#check λ (g : β → γ) (f : α → β) (x : α), g (f x)
                              -- (β → γ) → (α → β) → α → γ

#check λ (α β : Type) (b : β) (x : α), x
#check λ (α β γ : Type) (g : β → γ) (f : α → β) (x : α), g (f x)

#check (λ x : α, x) a                    -- α
#check (λ x : α, b) a                    -- β
#check (λ x : α, b) (h a b)              -- β
#check (λ x : α, g (f x)) (h (h a b) b)  -- β

#reduce (λ x : α, x) a                   -- a
#reduce (λ x : α, b) a                   -- b
#reduce (λ x : α, b) (h a b)             -- b
#reduce (λ x : α, g (f x)) (h (h a b) b) -- g (f (h (h a b) b))

#reduce (λ (Q R S : Type) (v : R → S) (u : Q → R) (x : Q),
       v (u x)) α β γ j g a              -- j (g a)

#print "reducing pairs"
#reduce (m, n).1        -- m
#reduce (m, n).2        -- n

#print "reducing boolean expressions"
#reduce tt && ff        -- ff
#reduce ff && b1        -- ff
#reduce b1 && ff        -- b1 && ff

#print "reducing arithmetic expressions"
#reduce n + 0           -- n
#reduce n + 2           -- nat.succ (nat.succ n)
#reduce 2 + 3           -- 5

-- #reduce 12345 * 54321   -- deep recursion was detected at 'replace' (potential solution: increase stack space in your system)
#eval 12345 * 54321

-- 2.4. Introducing Definitions

-- def `def_name` : `type` := `definition`

def foo : (ℕ → ℕ) → ℕ := λ f, f 0

#check foo
#print foo

def foo' := λ f : ℕ → ℕ, f 0

#check foo'
#print foo'

def double (x : ℕ) : ℕ := x + x
-- is equivalent to
def double' : ℕ → ℕ := λ x : ℕ, x + x

#print double
#check double 3
#reduce double 3                 -- 6
#reduce (double 3) - (double' 3) -- 0

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := sorry
def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := sorry

-- 2.5. Local Definitions

#check let y := 2 + 2 in y * y     -- ℕ
#reduce  let y := 2 + 2 in y * y   -- 16

def double_and_square (x : ℕ) : ℕ :=
let y := x + x in y * y

#reduce double_and_square 2   -- 16

#check   let y := 2 + 2, z := y + y in z * z   -- ℕ
#reduce  let y := 2 + 2, z := y + y in z * z   -- 64

def foobar := let a := nat in λ x : a, x + 2

-- def foobar' := (λ a, λ x : a, x + 2) nat   -- error

-- 2.6. Variables and Sections

section var
    variables (α β γ : Type)
    variables (g : β → γ) (f : α → β) (h : α → α)
    variable x : α

    def compose := g (f x)
    def do_twice := h (h x)
    def do_thrice := h (h (h x))

    #print compose
    #print do_twice
    #print do_thrice
end var

-- 2.7. Namespaces

namespace foo
  def a_number : ℕ := 5
  def function (x : ℕ) : ℕ := x + 7

  def fa : ℕ := function a_number
  def ffa : ℕ := function (function a_number)

  def some_name_only_inside_foo : ℕ := 42

  #print "inside foo"

  #check a_number
  #check function
  #check fa
  #check ffa
  #check foo.fa
end foo

#print "outside the namespace"

-- #check some_name_only_inside_foo -- error
#check foo.some_name_only_inside_foo

#check foo.a_number
#check foo.function
#check foo.fa
#check foo.ffa

section
    open foo

    #print "opened foo"

    #check a_number
    #check function
    #check fa
    #check foo.fa
end

-- #check a_number -- error

section
    open list

    #check @nil
    #check @cons
    #check @append
end

namespace blah
    def a : ℕ := 5
    def f (x : ℕ) : ℕ := x + 7
    def fa : ℕ := f a

    -- namespaces can be nested
    namespace inner
        def nothing : ℕ := 0
    end inner
end blah

#check blah.a
#check blah.f
#check blah.inner.nothing

-- namespaces can be re-opened

namespace blah
  def ffa : ℕ := f (f a)
end blah

-- 2.8. Dependent Types

-- a Pi type, or dependent function type
-- Π `\Pi`

-- the type Π x : α, β x denotes the type of functions f with the property that, 
-- for each a : α, f a is an element of β a. 

namespace list_pi

    constant list   : Type u → Type u

    constant cons   : Π α : Type u, α → list α → list α
    constant nil    : Π α : Type u, list α
    constant head   : Π α : Type u, list α → α
    constant tail   : Π α : Type u, list α → list α
    constant append : Π α : Type u, list α → list α → list α

end list_pi

namespace vec_pi
    constant vec : Type u → ℕ → Type u

    constant empty : Π α : Type u, vec α 0
    constant empty₁ : ∀ α : Type u, vec α 0

    constant cons :
        Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
    constant cons₁ :
        ∀ (α : Type u) (n : ℕ) (a : α), vec α n → vec α (n + 1)
    constant cons₂ :
        ∀ (α : Type u) (n : ℕ) (a : α) (van : vec α n), vec α (n + 1)

    constant append :
        Π (α : Type u) (n m : ℕ), vec α m → vec α n → vec α (n + m)
    constant append₀ :
        Π (α : Type u) (n m : ℕ) (van : vec α n) (vam : vec α m), vec α (n + m)

    -- They are equivalent
    #check cons
    #check cons₁
    #check cons₂

    -- They are equivalent
    #check append
    #check append₀
end vec_pi

-- Sigma types a.k.a dependent products

-- Pi types Π x : α, β x generalize the notion of 
-- a function type α → β by allowing β to depend on α

-- Sigma types Σ x : α, β x generalize the cartesian product α × β
-- in the same way:
-- in the expression sigma.mk a b, 
-- the type of the second element of the pair, b : β a, 
-- depends on the first element of the pair, a : α.

namespace sigma_type
    variable α : Type
    variable β : α → Type
    variable a : α
    variable b : β a

    #check sigma.mk a b      -- ⟨a, b⟩ : Σ (a : α), β a
    #check (sigma.mk a b).1  -- ⟨a, b⟩.fst : α
    #check (sigma.mk a b).2  -- β (sigma.fst (sigma.mk a b))
    -- ⟨a, b⟩.snd : (λ (a : α), β a) ⟨a, b⟩.fst

    #reduce  (sigma.mk a b).1  -- a
    #reduce  (sigma.mk a b).2  -- b
end sigma_type

-- 2.9. Implicit Arguments

namespace implicit_arguments 
    constant list : Type u → Type u

    namespace listish
        constant cons   : Π α : Type u, α → list α → list α
        constant nil    : Π α : Type u, list α
        constant append : Π α : Type u, list α → list α → list α

        -- Lean allows us to specify that this argument should, 
        -- by default, be left implicit.
        -- This is done by putting the arguments in curly braces
        constant consᵢ   : Π {α : Type u}, α → list α → list α
        constant nilᵢ    : Π {α : Type u}, list α
        constant appendᵢ : Π {α : Type u}, list α → list α → list α   

    end listish

    open listish

    variable  α : Type
    variable  a : α
    variables l1 l2 : list α

    #check cons α a (nil α)
    #check append α (cons α a (nil α)) l1
    #check append α (append α (cons α a (nil α)) l1) l2

    #check cons _ a (nil _)
    #check append _ (cons _ a (nil _)) l1
    #check append _ (append _ (cons _ a (nil _)) l1) l2

    #check consᵢ a nilᵢ
    #check appendᵢ (consᵢ a nilᵢ) l1
    #check appendᵢ (appendᵢ (consᵢ a nilᵢ) l1) l2

    namespace for_def
        def ident {α : Type u} (x : α) := x

        variables γ δ : Type u
        variables (c : γ) (d : δ)

        #check ident      -- ?M_1 → ?M_1
        #check @ident     -- ident : Π {α : Type u_1}, α → α
        #check ident c    -- γ
        #check ident d    -- δ
    end for_def

    namespace for_var
        variable { σ : Type u }
        variable x : σ
        def ident := x

        variables γ δ : Type u
        variables (c : γ) (d : δ)

        #check ident      -- ?M_1 → ?M_1
        #check @ident     -- ident : Π {σ : Type u_1}, σ → σ
        #check ident c    -- γ
        #check ident d    -- δ
    end for_var
end implicit_arguments

-- The process of instantiating these “holes,” or “placeholders,”
-- in a term is often known as elaboration. 

#check (2 : ℤ)

namespace ex_02_01
    def double (x : ℕ) : ℕ := x + x

    def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

    def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ)
    := λ op f, op (op f)

    #reduce Do_Twice do_twice double 2
    #reduce (pow 2 4) * 2

    example : 
    (Do_Twice do_twice double 2) = (double (double (double (double 2)))) :=
    by refl

end ex_02_01

namespace ex_02_02

    def curry {α β γ : Type} (f : α × β → γ) : α → β → γ :=
    λ a b, f (a, b)

    def uncurry {α β γ : Type} (f : α → β → γ) : α × β → γ :=
    λ ab, f ab.1 ab.2
    -- λ ⟨a, b⟩, f a b

    constant op : α × β → γ
    
    -- #check curry
    -- #check curry op

    lemma curry_uncurry {α β γ : Type} (f : α → β → γ) :
        curry (uncurry f) = f := 
    by refl

    #check (a, b)

    lemma uncurry_curry {α β γ : Type} (f : α × β → γ) :
        uncurry (curry f) = f :=
    -- funext (λ ⟨a, b⟩, rfl)
    begin
        -- simp only [curry, uncurry],
        rewrite curry,
        rewrite uncurry,
        apply funext,
        intro x,
        rewrite prod.mk.eta
    end

end ex_02_02

namespace ex_02_03

    constant vec : Type u → ℕ → Type u

    constant vec_add {n : ℕ} : vec ℕ n → vec ℕ n → vec ℕ n

    constant vec_reverse {α : Type} {n : ℕ} : vec α n → vec α n

    variables (v1 v2 : vec ℕ 5) (v3 : vec ℕ 7) (v4 : vec string 5)

    #check vec_add v1 v2
    -- #check vec_add v1 v3 -- errror: type mismatch
    -- #check vec_add v1 v4 -- errror: type mismatch

    #check vec_reverse v1
    #check vec_reverse v3
    #check vec_reverse v4
    #check vec_reverse (vec_add v1 v2)

end ex_02_03

namespace ex_02_04

    constant vec : Type u → ℕ → Type u

    constant matrix : Type u → ℕ → ℕ → Type u

    constant matrix_add {α : Type} {m n : ℕ} : matrix α m n → matrix α m n → matrix α m n

    -- https://www.mathsisfun.com/algebra/matrix-multiplying.html :)
    constant matrix_mul {α : Type} {m n p : ℕ} : matrix α m n → matrix α n p → matrix α m p

    constant matrix_vec_mul {α : Type} {m n p : ℕ} : matrix α m n → vec α n → vec α m

    variables (m1 : matrix ℕ 3 4) (m2 : matrix ℕ 4 5) (m3 : vec ℕ 3) (m4 : vec ℕ 4)

    #check matrix_add m1 m1
    -- #check matrix_add m1 m2 -- errror: type mismatch 
    #check matrix_mul m1 m2
    -- #check matrix_mul m1 m1 -- errror: type mismatch
    --#check matrix_mul m1 m3 -- errror: type mismatch
    -- #check matrix_vec_mul m1 m3 -- errror: type mismatch
    #check matrix_vec_mul m1 m4

end ex_02_04

-- 3. Propositions and Proofs
namespace chap_03

-- 3.1. Propositions as Types

constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant not : Prop → Prop
constant implies : Prop → Prop → Prop

constants p q r s : Prop
#check and p q                      -- Prop
#check or (and p q) r               -- Prop
#check implies (and p q) (and q p)  -- Prop

#check Prop -- Prop : Type
#check Type -- Type : Type 1

constant Proof : Prop → Type

constant local_and_comm : Π p q : Prop,
  Proof (implies (and p q) (and q p))

#check local_and_comm p q

constant local_modus_ponens :
  Π p q : Prop, Proof (implies p q) →  Proof p → Proof q

constant local_implies_intro :
  Π p q : Prop, (Proof p → Proof q) → Proof (implies p q)

-- Calculus of Constructions

-- Curry-Howard isomorphism a.k.a. propositions-as-types paradigm

-- Prop, like the other type universes, is closed under the arrow constructor: 
-- if we have p q : Prop, then p → q : Prop.

#check p → q -- Prop

#check α → β -- Type

#check Type u → Type v -- Type u → Type v : Type (max (u+1) (v+1))

-- Prop are definitionally proof-irrelevant types

-- 3.2. Working with Propositions as Types

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

#print t1
-- theorem chap_03.t1 : p → q → p :=
-- λ (hp : p) (hq : q), hp

-- Lean provides the alternative syntax assume for such a lambda abstraction:

theorem t1₂ : p → q → p :=
assume hp : p,
assume hq : q,
hp

#check t1₂ -- t1₂ : p → q → p

-- Lean also allows us to specify the type of the final term hp, explicitly, 
-- with a show statement.

theorem t1₃ : p → q → p :=
assume hp : p,
assume hq : q,
show p, from hp

#check t1₃ -- t1₃ : p → q → p

-- As with ordinary definitions, we can move the lambda-abstracted variables
-- to the left of the colon:

theorem t1₄ (hp : p) (hq : q) : p := hp

#check t1₄    -- t1₄ : p → q → p

-- the axiom command is alternative syntax for constant. 
-- Declaring a “constant” hp : p is tantamount to declaring that p is true, 
-- as witnessed by hp. 
axiom hp : p

#check hp -- hp : p

#check p
#check q
#check hp
#check t1₄
#check t1₄ hp

theorem t1₅ (p q : Prop) (hp : p) (hq : q) : p := hp

-- we can apply the theorem t1 just as a function application.
theorem t2 : q → p := t1₄ hp

theorem t1₆ (p q : Prop) (hp : p) (hq : q) : p := hp

theorem t1₇ : ∀ (p q : Prop), p → q → p :=
λ (p q : Prop) (hp : p) (hq : q), hp

#check t1₇

-- If p and q have been declared as variables, 
-- Lean will generalize them for us automatically:

variables p q : Prop

theorem t1₈ : p → q → p := λ (hp : p) (hq : q), hp

#check t1₈ -- t1₈ : ∀ (p q : Prop), p → q → p

variable  hp : p

theorem t1₉ : q → p := λ (hq : q), hp

#check t1₉ -- t1₉ : ∀ (p q : Prop), q → p

theorem t1ₐ (p q : Prop) (hp : p) (hq : q) : p := hp

variables r s : Prop

-- we can apply t1ₐ to different pairs of propositions, 
-- to obtain different instances of the general theorem.

#check t1ₐ p q                -- p → q → p
#check t1ₐ r s                -- r → s → r
#check t1ₐ (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable h : r → s
#check t1ₐ (r → s) (s → r) h  -- (s → r) → r → s

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) :
  γ :=
g (f x)

theorem t_compose (h₁ : q → r) (h₂ : p → q) : p → r :=
assume h₃ : p,
show r, from h₁ (h₂ h₃)

theorem t_compose₁ (h₁ : q → r) (h₂ : p → q) : p → r :=
λ h₃ : p,
h₁ (h₂ h₃)

#check t_compose₁

-- 3.3. Propositional Logic

#check true
#check false
#check tt
#check ff
#print notation ¬ -- \not, \neg
#check p ∧ q -- \and
#check p ∨ q -- \or 
#check p -> q
#check p → q -- \to, \r, \imp
#check p ↔ q -- \iff, \lr

#check p → q → p ∧ q
#check ¬p → p ↔ false
#check p ∨ q → q ∨ p

#print notation *  -- _ `*`:70 _:70 := has_mul.mul #1 #0
#print notation +  -- _ `+`:65 _:65 := has_add.add #1 #0
#print notation ¬  -- `¬`:40 _:40 := not #0
#print notation ∧ -- _ `∧`:35 _:34 := and #1 #0
#print notation ∨ -- _ `∨`:30 _:29 := or #1 #0
#print notation -> -- _ `->`:25 _:24 := #1 → #2
#print notation ↔  -- _ `↔`:20 _:20 := iff #1 #0

-- 3.3.1. Conjunction

example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check assume (hp : p) (hq : q), and.intro hp hq
#check λ (hp : p) (hq : q), and.intro hp hq

#check and.intro -- ?M_1 → ?M_2 → ?M_1 ∧ ?M_2
#check and.elim_left -- ?M_1 ∧ ?M_2 → ?M_1
#check and.elim_right -- ?M_1 ∧ ?M_2 → ?M_2

example (h : p ∧ q) : p := and.elim_left h
example (h : p ∧ q) : q := and.elim_right h

example (h : p ∧ q) : q ∧ p :=
and.intro (and.right h) (and.left h)

-- and-introduction and and-elimination are similar to 
-- the pairing and projection operations for the cartesian product

-- The similarity between ∧ and × is another instance of 
-- the Curry-Howard isomorphism, but in contrast to implication
--  and the function space constructor, 
-- ∧ and × are treated separately in Lean.

#check λ (p q : Prop) (hp : p) (hq : q), and.intro hp hq

#check λ (p q : Prop), (p, q)

-- #check λ (p q : Prop) (hp : p) (hq : q), (hp, hq) -- error

-- namespace hmn

-- variables m n : Prop
-- variable hm : m
-- variable hn : n

-- -- #check (hm, hn) --error

-- end hmn

-- the canonical way to construct an element is to apply and.intro to suitable arguments 
-- hp : p and hq : q.
-- Lean allows us to use anonymous constructor notation ⟨arg1, arg2, ...⟩ 
-- when the relevant type is an inductive type and can be inferred from the context.
-- In particular, we can often write ⟨hp, hq⟩ instead of and.intro hp hq

#check λ (p q : Prop) (hp : p) (hq : q), (⟨hp, hq⟩ : p ∧ q)

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := (|hp, hq|)

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

-- Given an expression e of an inductive type foo, 
-- the notation e.bar is shorthand for foo.bar e.

variable l : list ℕ

#check list.head l
#check l.head

example : list.head l == l.head :=
begin
refl
end

-- example (h : p ∧ q) : q ∧ p := and.intro (and.right h) (and.left h)

example (h : p ∧ q) : q ∧ p := ⟨ h.right, h.left ⟩

example (h : p ∧ q) : q ∧ p ∧ q:=
⟨h.right, ⟨h.left, h.right⟩⟩
-- is equivalent to
example (h : p ∧ q) : q ∧ p ∧ q:=
⟨h.right, h.left, h.right⟩

-- 3.3.2. Disjunction

example (hp : p) : p ∨ q := or.intro_left q hp
example (hq : q) : p ∨ q := or.intro_right p hq

example (h : p ∨ q) : q ∨ p :=
or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)

example : p ∨ q → q ∨ p :=
begin
    intro h,
    apply or.elim h,
    {
        apply or.intro_right
    },
    {
        apply or.intro_left
    }
end

example : p ∨ q → q ∨ p :=
assume h : p ∨ q,
or.elim h
  (assume hp : p,
    show q ∨ p, from or.intro_right q hp)
  (assume hq : q,
    show q ∨ p, from or.intro_left p hq)

example : p ∨ q → q ∨ p :=
λ h : p ∨ q,
or.elim h
  (λ hp : p, or.intro_right q hp)
  (λ hq : q, or.intro_left p hq)

example (h : p ∨ q) : q ∨ p :=
or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)

example (h : p ∨ q) : q ∨ p :=
h.elim
  (assume hp : p, or.inr hp)
  (assume hq : q, or.inl hq)

example (h : p ∨ q) : q ∨ p :=
h.elim
  (λ hp : p, or.inr hp)
  (λ hq : q, or.inl hq)

/-
inductive or (a b : Prop) : Prop
| inl (h : a) : or
| inr (h : b) : or

namespace or
  lemma elim (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → c) : c :=
  or.rec h₂ h₃ h₁
end or
-/

example (h : p ∨ q) : q ∨ p :=
begin
apply h.elim,
{
    intro hp,
    apply or.inr hp
},
{
    intro hq,
    apply or.inl hq
}
end

-- 3.3.3. Negation and Falsity

-- The type of ¬q is q → false

example (hpq : p → q) (hnq : ¬q) : ¬p := sorry

lemma nameless (hpq : p → q) (hnq : ¬q) : ¬p := sorry

#check nameless

def nameless₁ (hpq : p → q) (hnq : ¬q) : ¬p := sorry

def nameless₂ : (p → q) → (¬q) → ¬p := sorry

-- Play with `hpq` and `hnq` directly
def nameless₁' (hpq : p → q) (hnq : ¬q) : ¬p := (let play_with := (nameless₁ p q) in play_with hpq hnq)

-- Need Lambda to introduce binding names
def nameless₂' : (p → q) → (¬q) → ¬p :=  (let play_with := (nameless₁ p q) in λ hpq, λ hnq, (play_with hpq hnq)) -- need Lambda to introduce names for the type

lemma contrapositive_structural (hpq : p → q) (hnq : ¬q) : ¬p :=
assume hp : p,
show false, from hnq (hpq hp)

#print contrapositive_structural
-- theorem chap_03.contrapositive_structural : ∀ (p q : Prop), (p → q) → ¬q → ¬p :=
-- λ (p q : Prop) (hpq : p → q) (hnq : ¬q) (hp : p), show false, from hnq (hpq hp)

lemma contrapositive_structural_by_contradiction_sorry (hpq : p → q) (hnq : ¬q) : ¬p :=
by_contradiction
(assume hnnp : ¬¬p,
have hp : p, from sorry,
have hq : q, from sorry,
show false, from sorry)

lemma contrapositive_structural_by_contradiction (hpq : p → q) (hnq : ¬q) : ¬p :=
by_contradiction
(assume hnnp : ¬¬p,
have hp : p, from by_contradiction hnnp,
have hq : q, from hpq hp,
show false, from hnq hq)

#print contrapositive_structural_by_contradiction
-- theorem chap_03.contrapositive_structural_by_contradiction : ∀ (p q : Prop), (p → q) → ¬q → ¬p :=
-- λ (p q : Prop) (hpq : p → q) (hnq : ¬q),
--   by_contradiction
--     (λ (hnnp : ¬¬p), have hp : p, from by_contradiction hnnp, have hq : q, from hpq hp, show false, from hnq hq)

lemma contrapositive_tactic (hpq : p → q) (hnq : ¬q) : ¬p :=
begin
intro hp,
apply hnq,
apply hpq,
exact hp
end

#print contrapositive_tactic
-- theorem chap_03.contrapositive_tactic : ∀ (p q : Prop), (p → q) → ¬q → ¬p :=
-- λ (p q : Prop) (hpq : p → q) (hnq : ¬q), id (λ (hp : p), hnq (hpq hp))

lemma contrapositive_term (hpq : p → q) (hnq : q → false) : p → false :=
λ hp, hnq (hpq hp)

#print contrapositive_term
-- theorem chap_03.contrapositive_term : ∀ (p q : Prop), (p → q) → (q → false) → p → false :=
-- λ (p q : Prop) (hpq : p → q) (hnq : q → false) (hp : p), hnq (hpq hp)

lemma contrapositive_calc (hpq : p → q) (hnq : q → false) : p → false :=
calc p → q       : hpq
...    → false   : hnq

#print contrapositive_calc
-- theorem chap_03.contrapositive_calc : ∀ (p q : Prop), (p → q) → (q → false) → p → false :=
-- λ (p q : Prop) (hpq : p → q) (hnq : q → false), implies.trans hpq hnq

lemma contrapositive_calc₂ (p_to_q : p → q) (q_to_false : q → false) : p → false :=
calc p → q       : p_to_q
...    → false   : q_to_false

#print contrapositive_calc₂

theorem not_not_not_tactic
  (P : Prop) :
  ¬ ¬ ¬ P → ¬ P := 
begin
intro hnnnp,
intro hp,
apply hnnnp,
intro hnp,
apply hnp,
exact hp
end

theorem not_not_not_term
  (P : Prop) :
  ¬ ¬ ¬ P → ¬ P := 
λ hnnnp hp, hnnnp (λ hnp, hnp hp)

theorem not_not_not_calc_fancy
  (P : Prop) :
  ¬ ¬ ¬ P → ¬ P :=
calc ¬ ¬ ¬ P → ¬ P : iff.elim_left (not_not_not_iff P)

theorem not_not' (P : Prop) : ¬ (¬ P) → P :=
begin
  cases (classical.em P) with hp hnp,
  {
    intro hnnp,
    exact hp,
  },
  {
    intro hnnp,
    exfalso,
    apply hnnp,
    exact hnp
  }
end

theorem not_not_not_calc
  (P : Prop) :
  ¬ ¬ ¬ P → ¬ P :=
calc ¬ ¬ ¬ P  → ¬ P : not_not' (¬ P)


theorem not_not_not_structural
  (P : Prop) :
  ¬ ¬ ¬ P → ¬ P := 
assume hnnnp : ¬¬¬P,
assume hp : P,
have hnnp : ¬¬P, from (assume hnp: ¬P, hnp hp), -- from not_not_intro hp,
show false, from hnnnp hnnp

-- false.elim : ∀ {C : Prop}, false → C
-- This rule is sometimes called ex falso (short for ex falso sequitur quodlibet), or the principle of explosion.
example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)
-- absurd : ∀ {a b : Prop}, a → ¬a → b
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
absurd (hqp hq) hnp

-- 3.4. Introducing Auxiliary Subgoals

theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from and.intro (and.right h) (and.left h))
  (assume h : q ∧ p,
    show p ∧ q, from and.intro (and.right h) (and.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

theorem and_swap_term : p ∧ q ↔ q ∧ p :=
⟨(λ h : p ∧ q, ⟨h.right, h.left⟩),
  (λ h : q ∧ p, ⟨h.right, h.left⟩)⟩

theorem and_swap_tactic : p ∧ q ↔ q ∧ p :=
begin
split,
{
  intro h,
  apply and.intro h.right h.left
},
{
  intro h,
  apply and.intro h.right h.left
}
end

theorem and_swap_structural : p ∧ q ↔ q ∧ p :=
have lr : p ∧ q → q ∧ p, from (assume h : p ∧ q, ⟨h.right, h.left⟩),
have rl : q ∧ p → p ∧ q , from (assume h : q ∧ p, ⟨h.right, h.left⟩),
show p ∧ q ↔ q ∧ p, from iff.intro lr rl

theorem and_swap_calc : p ∧ q ↔ q ∧ p :=
have lr : p ∧ q → q ∧ p := calc p ∧ q → q ∧ p : (λ h : p ∧ q, ⟨h.right, h.left⟩),
have rl : q ∧ p → p ∧ q := calc q ∧ p → p ∧ q : (λ h : q ∧ p, ⟨h.right, h.left⟩),
show p ∧ q ↔ q ∧ p, from iff.intro lr rl

-- Because they represent a form of modus ponens, iff.elim_left and iff.elim_right 
-- can be abbreviated iff.mp and iff.mpr, respectively. I

example (h : p ∧ q) : q ∧ p := iff.mp (and_swap p q) h

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

-- the have construct introduces an auxiliary subgoal in a proof

-- Internally, the expression `have h : p, from s, t` produces the term `(λ (h : p), t) s`. 
-- In other words, s is a proof of p, t is a proof of the desired conclusion assuming h : p, 
-- and the two are combined by a lambda abstraction and application.

-- How to write proofs: a quick guide https://deopurkar.github.io/teaching/algebra1/cheng.pdf
-- Introduction to mathematical arguments https://deopurkar.github.io/teaching/algebra1/hutchings.pdf

example (h : p ∧ q) : q ∧ p :=
have hp : p, from and.left h,
suffices hq : q, from and.intro hq hp, -- prove q → what we're prooving
show q, from and.right h -- prove q

-- 3.5. Classical Logic

-- The introduction and elimination rules we have seen so far are all constructive, 
-- which is to say, they reflect a computational understanding of the logical connectives based on 
-- the propositions-as-types correspondence.

-- Ordinary classical logic adds to this the law of the "excluded middle", p ∨ ¬p. 
#check em p -- em p : p ∨ ¬p

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

example (h : ¬¬p) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, absurd h1 h)

example (h : ¬¬p) : p :=
by_contradiction
  (assume h1 : ¬p,
    show false, from h h1)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
or.elim (em p)
  (assume hp : p,
    or.inr
      (show ¬q, from
        assume hq : q,
        h ⟨hp, hq⟩))
  (assume hp : ¬p,
    or.inl hp)

-- example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
-- or.elim _ _ _

namespace ex_03_01

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
split,
{
  intro hpqr,
  apply and.intro,
  {
    apply hpqr.left.left
  },
  {
    apply and.intro hpqr.left.right hpqr.right
  }
},
{
  intro hpqr,
  apply and.intro,
  {
    apply and.intro hpqr.left hpqr.right.left
  },
  {
    apply hpqr.right.right
  }
}
end

-- example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
-- iff.intro
--   (assume hpqr : (p ∧ q) ∧ r, ⟨ _, _ ⟩)
--   (assume hpqr : p ∧ (q ∧ r), ⟨ _, _ ⟩)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (assume hpqr : (p ∧ q) ∧ r, ⟨ hpqr.left.left, ⟨ hpqr.left.right, hpqr.right ⟩ ⟩)
  (assume hpqr : p ∧ (q ∧ r), ⟨ ⟨ hpqr.left, hpqr.right.left ⟩, hpqr.right.right ⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
split,
{
  intro hpqr,
  apply hpqr.cases_on,
  {
    intro hpq,
    apply hpq.cases_on,
    {
      intro hp,
      apply or.intro_left (q ∨ r),
      exact hp
    },
    {
      intro hq,
      apply or.intro_right p,
      apply or.intro_left r,
      exact hq
    }
  },
  {
    sorry
  }
},
{
  sorry
}
end

-- example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
-- iff.intro
--   (assume hpqr : (p ∨ q) ∨ r, or.elim hpqr _ _)
--   (assume hpqr : p ∨ (q ∨ r), sorry)

-- copied from lemma or.assoc
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
  (or.rec (or.imp_right or.inl) (λ h, or.inr (or.inr h)))
  (or.rec (λ h, or.inl (or.inl h)) (or.imp_left or.inr))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
split,
{
  apply or.rec,
  {
    apply or.imp_right,
    apply or.inl,
  },
  {
    intro hr,
    apply or.inr,
    apply or.inr,
    exact hr
  }
},
{
  apply or.rec,
  {
    sorry
  },
  {
    sorry
  }
}
end

-- example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
-- iff.intro
--   (or.rec _ sorry)
--   (or.rec sorry sorry)

-- don't know how to synthesize placeholder
-- context:
-- p q r : Prop
-- ⊢ p ∨ q → p ∨ q ∨ r

/-

apply or.elim,

5 goals
p q r : Prop,
hpqr : p ∧ (q ∨ r)
⊢ ?m_1 ∨ ?m_2

p q r : Prop,
hpqr : p ∧ (q ∨ r)
⊢ ?m_1 → p ∧ q ∨ p ∧ r

p q r : Prop,
hpqr : p ∧ (q ∨ r)
⊢ ?m_1 → p ∧ q ∨ p ∧ r

p q r : Prop,
hpqr : p ∧ (q ∨ r)
⊢ Prop

-/

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
split,
{
  intro  hp_qr,
  apply or.elim,
  {
    /-
    1 goal
    p q r : Prop,
    hpqr : p ∧ (q ∨ r)
    ⊢ ?m_1 ∨ ?m_2
    -/
    exact hp_qr.right,
  },
  {
    sorry
  },
  {
    sorry
  },
  -- apply or.elim hp_qr.right,
  -- {
  --   intro hq,
  --   apply or.inl,
  --   apply and.intro,
  --   {
  --     exact hp_qr.left,
  --   },
  --   {
  --     exact hq,
  --   }
  -- },
},
{
  sorry
}
end

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (
    assume hp_qr : p ∧ (q ∨ r),
    have hp : p, from hp_qr.left,
    or.rec sorry sorry hp_qr.right
    -- or.elim hp_qr.right sorry sorry
  )
  (sorry)

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
have lr : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from sorry,
have rl : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r), from sorry,
show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r), from iff.intro lr rl

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
have lr : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from 
  (
    assume hp_qr : p ∧ (q ∨ r),
    have hp : p, from hp_qr.left,
    have hqr : q ∨ r, from hp_qr.right,
    have hq2c : q → (p ∧ q) ∨ (p ∧ r), from ( assume hq : q, or.inl ⟨hp, hq⟩ ),
    have hr2c : r → (p ∧ q) ∨ (p ∧ r), from ( assume hr : r, or.inr ⟨hp, hr⟩ ),
    or.elim hqr hq2c hr2c
  ),
have rl : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r), from
  (
    assume hpqpr : (p ∧ q) ∨ (p ∧ r),
    -- have hcq2p : p ∧ q → p, from (assume hpq : p ∧ q, hpq.left),
    -- have hcr2p : p ∧ r → p, from (assume hpr : p ∧ r, hpr.left),
    -- have hp : p, from or.elim hpqpr hcq2p hcr2p,
    -- have hp : p, from or.elim hpqpr (λ hpq : p ∧ q, hpq.left) (λ hpr : p ∧ r, hpr.left),
    -- have hqr : q ∨ r, from or.elim hpqpr (λ hpq : p ∧ q, or.inl hpq.right) (λ hpr : p ∧ r, or.inr hpr.right),

    -- have hp : p, from or.elim hpqpr (λ hpq, hpq.left) (λ hpr, hpr.left),
    -- have hqr : q ∨ r, from or.elim hpqpr (λ hpq, or.inl hpq.right) (λ hpr, or.inr hpr.right),

    or.elim hpqpr (λ hpq, ⟨hpq.left, (or.inl hpq.right)⟩) (λ hpr, ⟨hpr.left, or.inr hpr.right⟩)
  ),
show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r), from iff.intro lr rl

example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
  (
    assume hpqr : (p → (q → r)),
    show (p ∧ q → r), from (λ hpq, hpqr hpq.left hpq.right)
  )
  (
    assume hpqr : (p ∧ q → r),
    show (p → (q → r)), from (λ hp hq, hpqr ⟨hp, hq⟩)
  )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
  (
    assume hnpq : ¬(p ∨ q),
    have hnp : ¬p, from (λ hp, hnpq (or.inl hp)),
    have hnq : ¬q, from (λ hq, hnpq (or.inr hq)),
    show ¬p ∧ ¬q, from ⟨hnp, hnq⟩
  )
  (
    assume hnpnq : ¬p ∧ ¬q,
    show ¬(p ∨ q), from (λ hpq, or.elim hpq hnpnq.left hnpnq.right)
  )

example : (¬p ∨ q) → (p → q) :=
assume hnpq : (¬p ∨ q),
show (p → q), from (λ hp, or.elim hnpq (λ hnp, absurd hp hnp) (λ hq, hq))

example : (p → q) → (¬q → ¬p) :=
assume hp2q : (p → q),
show (¬q → ¬p), from (λ hnq, (λ hp, absurd (hp2q hp) hnq))

end ex_03_01

namespace ex_03_02

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
assume hp2rs : (p → r ∨ s),
have hnr2ps : ¬r → (p → s), from (
  assume hnr,
  assume hp,
  by_contradiction
  (
    assume hns : ¬s,
    or.elim (hp2rs hp) (λ hr, absurd hr hnr) (λ hs, absurd hs hns)
  )
),
have hrnr : r ∨ ¬r, from em r,
have hrpr : r → (p → r), from (λ hr hp, hr),
show ((p → r) ∨ (p → s)), from or.elim hrnr (λ hr, or.inl (hrpr hr)) (λ hnr, or.inr (hnr2ps hnr))

end ex_03_02

end chap_03
