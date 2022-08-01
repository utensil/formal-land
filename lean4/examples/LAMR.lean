/-!
======
LAMR
======

.. default-role:: lean4

Experimenting with code from https://github.com/avigad/lamr

3. Lean as a Programming Language
=====================================

3.1. About lean
------------------

https://avigad.github.io/lamr/using_lean_as_a_programming_language.html

-/

#check 2 + 2
#check -5
#check [1, 2, 3]
#check #[1, 2, 3]
#check Array
#check (1, 2, 3)
#check "hello world"
#check true
#check fun x => x + 1
#check λ x => x + 2
#check fun x => if x = 1 then "yes" else "no"

#check ([1, 2, 3] : List Nat)
#check (#[1, 2, 3] : Array Nat)

def isOne (x : Nat) : String := if x = 1 then "yes" else "no"
#check isOne
#print isOne

#check 2 + 2 < 5 ∧ isOne 3 = "no"

def Fermat_statement : Prop :=
∀ a b c n : Nat, a * b * c ≠ 0 ∧ n > 2 → a^n + b^n ≠ c^n

#check Fermat_statement

theorem two_plus_two_is_four : 2 + 2 = 4 := rfl

theorem Fermat_last_theorem : Fermat_statement := sorry

/-!

3.2. Using Lean as a functional programming language
----------------------------------------------------------------

-/

def printExample : IO Unit:= do
  IO.println "hello"
  IO.println "world"

#eval printExample

def factorial : Nat → Nat
  | 0       => 1
  | (n + 1) => (n + 1) * factorial n

#eval factorial 10
#eval factorial 100

def hanoi (numPegs start finish aux : Nat) : IO Unit :=
  match numPegs with
  | 0     => pure ()
  | n + 1 => do
      hanoi n start aux finish
      IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
      hanoi n aux finish start

#eval hanoi 7 1 2 3

def addNums : List Nat → Nat
  | []    => 0
  | a::as => a + addNums as

#eval addNums [0, 1, 2, 3, 4, 5, 6]

section
open List

#eval range 7
#eval addNums (range 7)
#eval addNums $ range 7
#eval map (fun x => x + 3) $ range 7
#eval map (. + 3) $ range 7
#eval foldl (. + .) 0 $ range 7
#check (. + .)

end

partial def gcd m n :=
  if n = 0 then m else gcd n (m % n)

/-!

3.3. Inductive data types in Lean
----------------------------------------------------------------

-/

section

inductive BinTree
  | empty : BinTree
  | node  : BinTree → BinTree → BinTree
  deriving Repr, DecidableEq, Inhabited

open BinTree

#eval node empty (node empty empty)

def size : BinTree → Nat
  | empty    => 0
  | node a b => 1 + size a + size b

def depth : BinTree → Nat
  | empty    => 0
  | node a b => 1 + Nat.max (depth a) (depth b)

def example_tree := node (node empty empty) (node empty (node empty empty))

#eval size example_tree
#eval depth example_tree

end

/-!

3.4. Using Lean as an imperative programming language
----------------------------------------------------------------

-/

def isPrime (n : Nat) : Bool := Id.run do
  if n < 2 then false else
    for i in [2:n] do
      if n % i = 0 then
        return false
      if i * i > n then
        return true
    true

#eval (List.range 10000).filter isPrime

def primes (n : Nat) : Array Nat := Id.run do
  let mut result := #[]
  for i in [2:n] do
    if isPrime i then
      result := result.push i
  result

#eval (primes 10000).size

/-!

5. Implementing Propositional Logic
================================================================

https://avigad.github.io/lamr/implementing_propositional_logic.html

5.1. Syntax
------------

An atomic formula is a variable or one of the constants ⊤ or ⊥. A literal is an atomic formula or a negated atomic formula.

The set of propositional formulas in negation normal form (NNF) is generated inductively as follows:

Each literal is in negation normal form.

If A and B are in negation normal form, then so are A ∧ B and A ∨ B.

Proposition

Every propositional formula is equivalent to one in negation normal form.

Proof

First use the identities A ↔ B ≡ (A → B) ∧ (B → A) and A → B ≡ ¬A ∧ B to get rid of ≡ and →. Then use De Morgan’s laws together with ¬¬A ≡ A to push negations down to the atomic formulas.

-/
section Props

inductive PropForm
  | tr     : PropForm
  | fls    : PropForm
  | var    : String → PropForm
  | conj   : PropForm → PropForm → PropForm
  | disj   : PropForm → PropForm → PropForm
  | impl   : PropForm → PropForm → PropForm
  | neg    : PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq

open PropForm

#check (impl (conj (var "p") (var "q")) (var "r"))

namespace PropForm

declare_syntax_cat propform

syntax "prop!{" propform "}"  : term

syntax:max ident                        : propform
syntax "⊤"                              : propform
syntax "⊥"                              : propform
syntax:35 propform:36 " ∧ " propform:35 : propform
syntax:30 propform:31 " ∨ " propform:30 : propform
syntax:20 propform:21 " → " propform:20 : propform
syntax:20 propform:21 " ↔ " propform:20 : propform
syntax:max "¬ " propform:40             : propform
syntax:max "(" propform ")"             : propform

macro_rules
  | `(prop!{$p:ident}) => `(PropForm.var $(Lean.quote p.getId.toString))
  | `(prop!{⊤})        => `(ProfForm.tr)
  | `(prop!{⊥})        => `(ProfForm.fls)
  | `(prop!{¬ $p})     => `(PropForm.neg prop!{$p})
  | `(prop!{$p ∧ $q})  => `(PropForm.conj prop!{$p} prop!{$q})
  | `(prop!{$p ∨ $q})  => `(PropForm.disj prop!{$p} prop!{$q})
  | `(prop!{$p → $q})  => `(PropForm.impl prop!{$p} prop!{$q})
  | `(prop!{$p ↔ $q})  => `(PropForm.biImpl prop!{$p} prop!{$q})
  | `(prop!{($p:propform)}) => `(prop!{$p})

private def toString : PropForm → String
  | var s    => s
  | tr       => "⊤"
  | fls      => "⊥"
  | neg p    => s!"(¬ {toString p})"
  | conj p q => s!"({toString p} ∧ {toString q})"
  | disj p q => s!"({toString p} ∨ {toString q})"
  | impl p q => s!"({toString p} → {toString q})"
  | biImpl p q => s!"({toString p} ↔ {toString q})"

instance : ToString PropForm := ⟨PropForm.toString⟩

end PropForm

#check prop!{p ∧ q → (r ∨ ¬ p) → q}
#eval prop!{p ∧ q → (r ∨ ¬ p) → q}
#check prop!{p ∧ q ∧ r → p}

def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

/-!
Minimal enhancement for List related examples:
-/
namespace List

def insert [DecidableEq α] (a : α) (l : List α) : List α :=
  if a ∈ l then l else a :: l

protected def union [DecidableEq α] (l₁ l₂ : List α) : List α :=
  foldr insert l₂ l₁

end List

namespace PropForm

def complexity : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => complexity A + 1
  | conj A B => complexity A + complexity B + 1
  | disj A B => complexity A + complexity B + 1
  | impl A B => complexity A + complexity B + 1
  | biImpl A B => complexity A + complexity B + 1

def depth : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => depth A + 1
  | conj A B => Nat.max (depth A) (depth B) + 1
  | disj A B => Nat.max (depth A) (depth B) + 1
  | impl A B => Nat.max (depth A) (depth B) + 1
  | biImpl A B => Nat.max (depth A) (depth B) + 1

def vars : PropForm → List String
  | var s => [s]
  | tr => []
  | fls => []
  | neg A => vars A
  | conj A B => (vars A).union (vars B)
  | disj A B => (vars A).union (vars B)
  | impl A B => (vars A).union (vars B)
  | biImpl A B => (vars A).union (vars B)

end PropForm

/-!

5.2. Semantics
----------------

-/

-- Minimal implementation for PropAssignment examples
def PropAssignment := List (String × Bool)

namespace PropAssignment

def mk (vars : List (String × Bool)) : PropAssignment :=
  vars

def eval? (τ : PropAssignment) (var : String) : Option Bool := Id.run do
  let τ : List _ := τ
  for (k, v) in τ do
    if k == var then return some v
  return none

def eval (τ : PropAssignment) (var : String) : Bool :=
  τ.eval? var |>.getD false

end PropAssignment

def PropForm.eval (v : PropAssignment) : PropForm → Bool
  | var s => v.eval s
  | tr => true
  | fls => false
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))

#eval let v := PropAssignment.mk [("p", true), ("q", true), ("r", true)]
      prop!{p ∧ q ∧ r → p}.eval v

end Props
