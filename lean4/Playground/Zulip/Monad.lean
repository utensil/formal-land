/-

  From https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Ensuring.20naive.20purity

  Will revisit later

-/

-- def natFun : Nat → ByteArray :=
--   IO.getRandomBytes 8 |>.run'

--   -- | k => match (IO.getRandomBytes 8 |>.run' ()) with
--   --   | some bytes => bytes.toUInt64BE!.toNat % 256
--   --   | none => k

-- -- #eval natFun 4

/-

type mismatch
  EStateM.set s
has type
  EStateM ?m.273 (?m.61 → EStateM.Result ?m.60 ?m.61 ?m.61) PUnit : Type
but is expected to have type
  Id Unit : Type

-/
-- def ohNo : Unit := Id.run do
--   let s ← EStateM.get
--   IO.println "Oh no"
--   EStateM.set s

-- #eval ohNo



def anyway : IO Unit := do
  -- v4.32: `IO` is no longer an `EStateM`, so the naive-purity attempt below no longer
  -- typechecks (see the live `ohNo` guard); the remainder of the experiment just draws
  -- random bytes without touching any state.
  let x := ← (·.toUInt64BE!.toNat % 256) <$> IO.getRandomBytes 8
  let y := ← (·.toUInt64BE!.toNat % 256) <$> IO.getRandomBytes 8
  let z := ← (·.toUInt64BE!.toNat % 256) <$> IO.getRandomBytes 8
  IO.println f!"{x} {y} {z}"
-- v4.32: `IO.getRandomBytes` depends on a `sorry`-based core definition, so plain `#eval` aborts;
-- use `#eval!` to force evaluation.
#eval! anyway

/-!
The naive-purity attempt itself now fails to typecheck (previously `IO` was an `EStateM`, so
`EStateM.get`/`EStateM.set` compiled). The guard keeps the failure visible while the file still
elaborates.
-/
/--
error: Type mismatch
  IO.println "Oh no"
has type
  IO Unit
but is expected to have type
  Id Unit
---
error: Type mismatch
  EStateM.set s
has type
  EStateM ?m.9 (?m.4 → EStateM.Result ?m.3 ?m.4 ?m.4) PUnit
but is expected to have type
  Id Unit
-/
#guard_msgs in
def ohNo : Unit := Id.run do
  let s ← EStateM.get
  IO.println "Oh no"
  EStateM.set s


example : 1 + 1 = 2 := by
  rfl
  done


structure Two where
  x : Nat
  property : x = 2 := by decide

def a : Two := {x := 2}
def b := Two.mk 2
def c : Two := ⟨2, rfl⟩ -- hope to omit rfl
