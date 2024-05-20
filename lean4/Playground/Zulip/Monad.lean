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
  let s ← EStateM.get
  let x := ← (·.toUInt64BE!.toNat % 256) <$> IO.getRandomBytes 8
  -- EStateM.set s
  let y := ← (·.toUInt64BE!.toNat % 256) <$> IO.getRandomBytes 8
  -- EStateM.set s
  let z := ← (·.toUInt64BE!.toNat % 256) <$> IO.getRandomBytes 8
  IO.println f!"{x} {y} {z}"
#eval anyway


example : 1 + 1 = 2 := by
  rfl
  done


structure Two where
  x : Nat
  property : x = 2 := by decide

def a : Two := {x := 2}
def b := Two.mk 2
def c : Two := ⟨2, rfl⟩ -- hope to omit rfl
