import Lean
-- import Batteries.Util.TermUnsafe

open Lean Meta Elab Command Tactic

abbrev Entry := String
abbrev EntryList := List Entry

-- Lean server printed an error: libc++abi: terminating due to uncaught exception of type lean::exception: cannot evaluate `[init]` declaration 'proofStatesExt' in the same module

initialize myExt : SimplePersistentEnvExtension Entry EntryList ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.concat)
    addImportedFn := mkStateFromImportedEntries (·.concat) {}
    -- v4.32: `modifyEnv` from a tactic runs in the declaration's async environment branch,
    -- and the default `.mainOnly` mode panics there; `.local` permits the modification.
    asyncMode := .local
  }

elab (name := Proof) "Proof" _desc:interpolatedStr(term)* ":" _t:tacticSeq : tactic => do
  unsafe enableInitializersExecution

  modifyEnv fun env =>
    myExt.addEntry env ""
