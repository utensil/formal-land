import Lean.Elab

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

instance : Monad <| WithLog logged where
  pure val := ⟨[], val⟩
  bind item next :=
    let rec nextItem := next item.val
    ⟨item.log ++ nextItem.log, nextItem.val⟩

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.all true
set_option pp.analyze true
set_option trace.Meta.synthInstance true
set_option synthInstance.checkSynthOrder true

def Option' := Option

/--
error: fields missing: 'map', 'mapConst', 'seq', 'seqLeft'
-/
#guard_msgs(error, drop info) in
instance : Monad Option' where
  pure := Option.some
  bind a f :=
    let b := Option.bind a f
    b

variable (logged : Type) in
#synth Monad <| WithLog logged

-- instance : Pure <| WithLog logged where
--   pure val := ⟨[], val⟩

-- -- instance : Bind <| WithLog logged where
-- --   bind item next :=
-- --     let {log := thisLog, .. } := item
-- --     let {log := nextOut, val := nextRes} := next item.val
-- --     ⟨thisLog ++ nextOut, nextRes⟩

-- instance : Bind <| WithLog logged where
--   bind item next :=
--     let nextItem := next item.val
--     ⟨item.log ++ nextItem.log, nextItem.val⟩

-- section CheckInstances

-- variable (logged : Type)

-- /-
-- failed to synthesize
--   Applicative (WithLog logged)
-- -/
-- #synth Applicative <| WithLog logged

-- /-
-- failed to synthesize
--   Monad (WithLog logged)
-- -/
-- #synth Monad <| WithLog logged

-- /-
-- [Meta.synthInstance] ✅ Monad (WithLog logged) ▼
--   [] new goal Monad (WithLog logged) ▶
--   [] ✅ apply @instMonadWithLog to Monad (WithLog logged) ▼
--     [tryResolve] ✅ Monad (WithLog logged) ≟ Monad (WithLog logged)
--   [] result instMonadWithLog
-- -/
-- #synth Monad <| WithLog logged

-- end CheckInstances

-- /-
-- [Meta.synthInstance] ❌ Applicative (WithLog logged) ▶


-- [Meta.synthInstance] ❌ Functor (WithLog logged) ▶


-- [Meta.synthInstance] ✅ Pure (WithLog logged) ▶


-- [Meta.synthInstance] ❌ Seq (WithLog logged) ▶


-- [Meta.synthInstance] ❌ SeqLeft (WithLog logged) ▶


-- [Meta.synthInstance] ❌ SeqRight (WithLog logged) ▶


-- [Meta.synthInstance] ✅ Bind (WithLog logged) ▶
-- -/
-- instance : Monad <| WithLog logged where -- no error

-- variable (logged : Type) in
-- #synth Monad <| WithLog logged

-- def Option' := Option

-- #print Monad.map._default

-- structure A where
--   a : Nat -> Nat := fun x => x

-- structure B extends A where
--   a := A.a._default

/-
@[reducible] def Applicative.map._default.{u_1, u_2} : {f : Type u_1 → Type u_2} →
  Pure.{u_1, u_2} f → Seq.{u_1, u_2} f → {α β : Type u_1} → (α → β) → f α → f β :=
fun {f : Type u_1 → Type u_2} (toPure : Pure.{u_1, u_2} f) (toSeq : Seq.{u_1, u_2} f) =>
  @id.{max (u_1 + 2) (u_2 + 1)} ({α β : Type u_1} → (α → β) → f α → f β) fun {α β : Type u_1} (x : α → β) (y : f α) =>
    @Seq.seq.{u_1, u_2} f toSeq α β (@Pure.pure.{u_1, u_2} f toPure (α → β) x) fun (x : Unit) => y
-/
#print Applicative.map._default

/-
@[reducible] def Monad.map._default.{u_1, u_2} : {m : Type u_1 → Type u_2} →
  Applicative m → Bind m → {α β : Type u_1} → (α → β) → m α → m β :=
fun {m} toApplicative toBind => @id ({α β : Type u_1} → (α → β) → m α → m β) fun {α β} f x => x >>= pure ∘ f
-/
#print Monad.map._default

set_option structureDiamondWarning true

-- instance : Monad Option' where
--   pure := Option.some
--   bind := Option.bind
--   map := Monad.map._default

-- instance : Monad Option' where
--   pure := Option.some
--   bind a f :=
--     let b := Option.bind a f
--     b
--   map f x := Monad.map._default _ _ f x

-- instance : Monad Option' where
--   pure := Option.some
--   bind a f :=
--     let rec b := Option.bind a f
--     b
--   map f x := Monad.map._default _ _ f x

instance : Monad Option' where
  pure := Option.some
  bind a f :=
    let c :=
      let rec b := Option.bind a f
      b
    c


#check Lean.Elab.Term.elabLetDecl
#check Lean.Elab.Term.elabLetRec
#check Lean.Elab.Structural.preprocess
#check Lean.Elab.Command.elabStructure
