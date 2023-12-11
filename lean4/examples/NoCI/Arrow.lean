import Lean
import Std.Tactic.GuardMsgs
open Lean System

/-!
  From https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/unknown.20identifier.20in.20.60let.20var.20.3A.3D.20if.20let.60
-/

def getOpt (str : String) : Option String := str

def getIO (str : String) : IO String := pure str

def getOptIO (str : String) : IO (Option String) := pure (some str)

/-!
  ## Initial problem

  ### Case `if let return` works
-/
def works₁ : IO String := do
  if let some opt := getOpt "str" then
    let ret := (<- getIO opt)
    return ret
  else
    return "none"

#eval works₁ -- works "str"

/-!
  ### Case `let var <- if let` also works
-/
def works₂ : IO String := do
  let var <- if let some opt := getOpt "str" then
    let ret := (<- getIO opt)
    pure ret
  else
    pure "none"

  return var

#eval works₂ -- works: "str"

/-!
  ### Case `let var := if let` gives `unknown identifier`
-/


/--
error: unknown identifier 'opt'
-/
#guard_msgs in
def oops₀ : IO String := do
  let var := if let some opt := getOpt "str" then
    let ret := (<- getIO opt)  -- unknown identifier 'opt'
    ret
  else
    "none"

  return var

/-!
  ## More variants

  ### Variant 1. expect `<-`, misuse `:=`

  #### 1.1 expect `<-`, misuse `:=`, gives `unknown identifier`
-/
/--
error: unknown identifier 'ret'
-/
#guard_msgs in
def oops₁₁ : IO String := do
  let some ret := getOptIO "str"
  ret -- unknown identifier 'ret'

/-!
  #### 1.2 expect `<-`, misuse `:=`, gives `type mismatch`
-/

/--
error: type mismatch
  some ret
has type
  Option ?m.2842 : Type
but is expected to have type
  IO (Option String) : Type
-/
#guard_msgs in
def oops₁₂ : IO String := do
  let some ret := getOptIO "str" | pure "none" -- type mismatch: `IO (Option String)` got `Option ?m.2842`
  pure ret

/-!
  #### 1.3 using `<-` works
-/
def works₁₃ : IO String := do
  let some ret <- getOptIO "str" | pure "none"
  pure ret -- works


/-!
  ### Variant 2. expect `:=`, misuse `<-`, gives `type mismatch`
-/

/--
error: type mismatch
  io
has type
  String : Type
but is expected to have type
  IO String : Type
-/
#guard_msgs in
def oops₂ : IO String := do
  let io <- getIO "str"
  io -- type mismatch: expected `IO String`, got `String`

/-!
  ### Variant 3. in `if let`, expect `:=`, misuse `<-`
-/

def oops₃ : IO String := do
  if let some opt <- getOpt "str" then  -- unexpected token '<-'; expected ':=' or '←'
    let ret := (<- getIO opt)
    return ret
  else
    return "none"

/-!
  ### Variant 4. in `if let`, expect `:= (<- ... )`

  #### 4.1 misuse `:=` gives me type mismatch
-/

/--
error: type mismatch
  some opt
has type
  Option ?m.4322 : Type
but is expected to have type
  IO (Option String) : Type
-/
#guard_msgs in
def oops₄₁ : IO String := do
  if let some opt := getOptIO "str" then -- type mismatch: expected `IO (Option String)`, got `Option ?m.3586`
    let ret <- getIO opt
    pure ret
  else
    pure "none"

/-!
  #### 4.2 misuse `<-` gives me `unexpected token '<-'; expected ':=' or '←'`
-/
def oops₄₂ : IO String := do
  if let some opt <- getOptIO "str" then -- unexpected token '<-'; expected ':=' or '←'
    let ret <- getIO opt
    pure ret
  else
    pure "none"

/-!
  #### 4.3 using `:= (<- ... )` works
-/
def works₄₃ : IO String := do
  if let some opt := (<- getOptIO "str") then
    let ret <- getIO opt
    pure ret
  else
    pure "none"


/-!
  ## Cases from https://github.com/leanprover/lean4/pull/2676
-/

/--
error: application type mismatch
  pure true
argument
  true
has type
  Bool : Type
but is expected to have type
  Unit : Type
---
error: application type mismatch
  pure false
argument
  false
has type
  Bool : Type
but is expected to have type
  Unit : Type
-/
#guard_msgs in
example : IO Unit := do
  let x ← if true then pure true else pure false

/--
error: unknown identifier 'x'
---
error: unknown identifier 'x'
---
error: unknown identifier 'x'
-/
#guard_msgs in
example : Id Unit := do
  let mut x ← if true then pure true else pure false
  if let .true := x then
    x := false
