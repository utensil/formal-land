import Mathlib.Testing.SlimCheck.Functions

/--
info:
---
error:
===================
Found problems!
x := 0
y := 0
issue: 0 ≠ 0 does not hold
(0 shrinks)
-------------------
-/
#guard_msgs (whitespace := lax) in
#eval SlimCheck.Testable.check (∀ (x y : Nat), x + y ≠ y + x)

instance SlimCheck.Testable.existsTestable (p : Prop) {β : α → Prop}
  [Testable (NamedBinder var (∀ x, NamedBinder var $ β x → p))] :
  Testable (NamedBinder var (NamedBinder var (∃ x, β x) → p)) where
  run := λ cfg min => do
    let x ← Testable.runProp (NamedBinder var (∀ x, NamedBinder var $ β x → p)) cfg min
    pure $ SlimCheck.TestResult.iff exists_imp x

#eval SlimCheck.Testable.check (∀ (x y : Nat), x + y = y + x)

lemma ex1 : ∀ (v : Nat × Nat), v.1 + v.2 = v.2 + v.1 := by
  exact fun v => Nat.add_comm v.1 v.2

lemma ex2 : ∀ (v : Nat × Nat), v.1 + v.2 ≠ v.2 + v.1 → false := by
  intro h
  simp?
  exact?

#eval SlimCheck.Testable.check (∀ (v : Nat × Nat), v.1 + v.2 ≠ v.2 + v.1 → false)

-- set_option trace.Meta.synthInstance true in
-- #eval SlimCheck.Testable.check (∃ (v : Nat × Nat), v.1 + v.2 ≠ v.2 + v.1 → false)

lemma ex'' : ∀ (x y : Nat), x + y = y + x := by
  exact Nat.add_comm

example : (∃ (x y : Nat), x + y ≠ y + x) → false := by
  intro h
  obtain ⟨x, y, h⟩ := h
  have h' : x + y = y + x := ex'' x y
  contradiction
