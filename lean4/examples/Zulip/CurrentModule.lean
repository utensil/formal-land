-- From a wechat group question
import Lean

open Lean Elab Command Meta Tactic

syntax "currentModule" : term
elab_rules : term
| `(currentModule) => do
  return Lean.mkStrLit s!"{ (← getEnv).header.mainModule }"

def main : IO Unit := do
  IO.println s!"{currentModule}"

#eval main
