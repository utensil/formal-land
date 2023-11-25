/-
Inspired by https://leanprover.zulipchat.com/#narrow/stream/236449-Program-verification/topic/.E2.9C.94.20Small-step.20operational.20semantics
-/
import Std.Tactic.Basic
import Std.Tactic.RCases
import Std.CodeAction

inductive Tm where
| C : Nat → Tm
| P : Tm → Tm → Tm

namespace Tm

def evalF: Tm → Nat
| C n => n
| P l r => l.evalF + r.evalF

set_option hygiene false in
infixl:25 " ==> " => eval

inductive eval : Tm → Nat → Prop where
| EConst : ∀ n, C n ==> n
| EPlus : ∀ t₁ t₂ n₁ n₂,
    t₁ ==> n₁ →
    t₂ ==> n₂ →
    P t₁ t₂ ==> n₁ + n₂

-- Repeating this helps delaboration
infixl:25 " ==> " => eval

set_option hygiene false in
infixl:25 " ~~> " => step

inductive step : Tm → Tm → Prop where
| StPlusConstConst :
    P (C n₁) (C n₂) ~~> C (n₁ + n₂)
| StPlusLeft (t₁ t₁' t₂ : Tm):
    t₁~~>t₁' →
    P t₁ t₂ ~~> P t₁' t₂
| StPlusRight (t₂ t₂' : Tm):
    t₂ ~~> t₂' →
    P (C n) t₂ ~~> P (C n) t₂'

-- Repeating this helps delaboration
infixl:25 " ~~> " => step

end Tm

def Relation (α: Type) := α → α → Prop

def Relation.deterministic (R: Relation α) : Prop :=
  ∀ {x y₁ y₂: α}, R x y₁ → R x y₂ → y₁ = y₂

theorem EvalSmallStep.deterministic : Relation.deterministic Tm.step := by
  unfold Relation.deterministic
  intro x y₁ y₂ hy₁ hy₂
  induction hy₁ generalizing y₂ with
  | StPlusConstConst =>
    -- cases hy₂ <;> rename_i h₂ <;> first | rfl | cases h₂
    cases hy₂ with
    | StPlusConstConst => rfl
    | @StPlusLeft _ _ _ hl => cases hl
    | @StPlusRight _ _ _ hr => cases hr
  | @StPlusLeft _ _ _ hl hPl =>
    cases hy₂ with
    | StPlusConstConst => contradiction
    | @StPlusLeft _ _ _ hl' => rw [hPl hl']
    | StPlusRight => cases hl
  | @StPlusRight _ _ _ hr hPr =>
    cases hy₂ with
    | StPlusConstConst => contradiction
    | @StPlusLeft _ _ _ hl' => cases hl'
    | @StPlusRight _ _ _ hr' => rw [hPr hr']
  done
