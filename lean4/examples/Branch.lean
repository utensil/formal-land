import Lean
import Mathlib.Tactic

open Lean Meta Elab Command Tactic

/-!
  Inspired by
  
  - [Lean auto grader](https://github.com/adamtopaz/lean_grader)
  - [`Branch` in lean4game](https://github.com/leanprover-community/lean4game/blob/main/server/GameServer/Commands.lean), see also [its doc](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#proof)
  - [`tada` on Zulip`](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Lean.203.20or.204.3F/near/394490716)
-/
-- structure ProofState where
--   (desc : String)
--   (proven : Bool)
--   (sorries : Bool)
--   (errors : Bool)
--   deriving Inhabited, BEq, Repr, Hashable

-- abbrev ProofStateSet := List ProofState

-- initialize proofs : PersistentEnvExtension (Name × Game) (Name × Game) (HashMap Name Game) ←
--   do registerPersistentEnvExtension {
--     name          := `gameExt,
--     mkInitial     := pure {},
--     addImportedFn := fun ess => do
--       let mut games := {}
--       for es in ess do
--         for (name, game) in es do
--           match games.find? name with
--           | some oldgame =>
--             games := games.insert name (Game.merge oldgame game)
--           | none =>
--             games := games.insert name game
--       return games
--     addEntryFn    := (λ s n => s.insert n.1 n.2),
--     exportEntriesFn := HashMap.toArray,
--     statsFn := fun s => format "number of local entries: " ++ format s.size
-- }

-- elab "add_proof" : command => do
--   modifyEnv λ env =>
--     let constants := env.constants.insert `falso $ ConstantInfo.thmInfo
--       { name := `falso
--         levelParams := []
--         type := .const ``False []
--         value := .const ``False []
--       }
--     { env with constants }

-- partial def collectProofs (stx : Syntax) (acc : Proofs := []) : CommandElabM Proofs := do
--   match stx with
--   | .missing => return acc
--   | .node _info kind args =>
--     if kind == `Proof || kind == `QED then return acc
--     return ← args.foldlM (fun acc arg => collectProofs arg acc) acc
--   | .atom _info val =>
--     -- ignore syntax elements that do not start with a letter
--     -- and ignore some standard keywords
--     let allowed := ["with", "fun", "at", "only", "by"]
--     if 0 < val.length ∧ val.data[0]!.isAlpha ∧ not (allowed.contains val) then
--       let val := val.dropRightWhile (fun c => c == '!' || c == '?') -- treat `simp?` and `simp!` like `simp`
--       return {acc with tactics := acc.tactics.insert val}
--     else
--       return acc
--   | .ident _info _rawVal val _preresolved =>
--       let ns ←
--         try resolveGlobalConst (mkIdent val)
--         catch | _ => pure [] -- catch "unknown constant" error
--       return ← ns.foldlM (fun acc n => do
--         if let some (.thmInfo ..) := (← getEnv).find? n then
--           return {acc with lemmas := acc.lemmas.insertMany ns}
--         else
--           return {acc with definitions := acc.definitions.insertMany ns}
--       ) acc

-- elab doc:docComment ? attrs:Parser.Term.attributes ?
--     "Theorem" theoremName:ident ? sig:declSig val:declVal : command => do

  -- let proofs ← match val with
  -- | `(Parser.Command.declVal| := $proof:term) => do
  --   collectProofs proof
  -- | _ => throwError "expected `:=`"

-- initialize proofStatesExt : SimplePersistentEnvExtension ProofState ProofStateSet ←
--   registerSimplePersistentEnvExtension {
--     addEntryFn := (·.concat)
--     addImportedFn := mkStateFromImportedEntries (·.concat) {}
--   }

-- elab (name := Proof) "Proof" _desc:interpolatedStr(term)* ":" t:tacticSeq : tactic => do
--   let env : Environment <- getEnv
--   let axioms := (CollectAxioms.collect `foo |>.run env |>.run {}).snd.axioms

--   let b ← saveState
--   evalTactic t

--   let gs ← getUnsolvedGoals
--   if !gs.isEmpty then
--     let msgs ← Core.getMessageLog
--     logWarning "This branch leaves open goals."
--     Core.setMessageLog msgs
--   -- else
--   --   modifyEnv fun env =>
--   --     proofStatesExt.addEntry env {
--   --       desc := " "
--   --       proven := gs.isEmpty
--   --       sorries := false
--   --       errors := false
--   --     }

--   let msgs ← Core.getMessageLog
--   b.restore
--   Core.setMessageLog msgs

-- def appendGoals (mvarIds : List MVarId) : TacticM Unit :=
--   modify fun s => { s with goals := s.goals ++ mvarIds }
-- def dup (gs : List MVarId) : List MVarId :=
--   gs.map fun g => 
--     let g' : MVarId := g -- { g with name := mkSimple "proof" }
--     g'

elab "proofs " n:num : tactic => do
  let goals ← getGoals
  let m := n.1.toNat
  let goalsDup := List.range m |>.foldl (init := []) fun acc _ => acc ++ goals
  setGoals $ goalsDup

elab (name := proof) "proof" _n:(num)? _desc:interpolatedStr(term)? ":" t:tacticSeq : tactic => do
  let mvarId :: mvarIds ← getUnsolvedGoals | throwNoGoalsToBeSolved
  setGoals [mvarId]
  let b ← saveState
  let a <- evalTactic t
  -- let gs ← getUnsolvedGoals
  -- if !gs.isEmpty then
  --   let msgs ← Core.getMessageLog
  --   logWarning "This branch leaves open goals."
  --   Core.setMessageLog msgs

  let msgs ← Core.getMessageLog
  b.restore
  setGoals mvarIds
  Core.setMessageLog msgs
  
  pure a

elab (name := QED) "QED" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logInfo " 🎉 Goals accomplished"
  else
    logError "☝️ Unresolved goals"

elab (name := WIP) "WIP" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logError " 🎉 Goals accomplished, mark it with QED"
  else
    logWarning "☝️ Unresolved goals"

example (a b c : ℕ) : a + b * c = c * b + a := by
  proofs 2
  proof 1:
    rw [Nat.add_comm, @Nat.add_right_cancel_iff, Nat.mul_comm]
    QED
  proof 2:
    ring
    QED

example : 1 + 2 = 3 := by
  proofs 5
  proof "trivial":
    rfl
    QED
  proof "automatic":
    simp
    QED
  proof "cheating":
    sorry
    QED
  proof "WIP":
    rewrite [Nat.add_comm]
    WIP
  proof "verbose":
    have h : 1 + 2 = 3 := by rfl
    exact h
    QED
  
