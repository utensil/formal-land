/-
  https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/unknown.20identifier.20in.20.60let.20var.20.3A.3D.20if.20let.60
-/

import Lean
open Lean System

def getOpt (str : String) : Option String := str

def getIO (str : String) : IO String := pure str

def getOptIO (str : String) : IO (Option String) := pure (some str)

-- if let return
def works₁ : IO String := do
  if let some opt := getOpt "str" then
    let ret := (<- getIO opt)
    return ret
  else
    return "none"

#eval works₁ -- works "str"

-- let var <- if let
def works₂ : IO String := do
  let var <- if let some opt := getOpt "str" then
    let ret := (<- getIO opt)
    pure ret
  else
    pure "none"

  return var

#eval works₂ -- works: "str"

-- let var := if let
def oops₀ : IO String := do
  let var := if let some opt := getOpt "str" then
    let ret := (<- getIO opt)  -- unknown identifier 'opt'
    ret
  else
    "none"

  return var

-- 1. expect `<-`, misuse `:=`

def oops₁₁ : IO String := do
  let some ret := getOptIO "str"
  ret -- unknown identifier 'ret'

def oops₁₂ : IO String := do
  let some ret := getOptIO "str" | pure "none" -- type mismatch: `IO (Option String)` got `Option ?m.2842`
  pure ret

def works₁₃ : IO String := do
  let some ret <- getOptIO "str" | pure "none"
  pure ret -- works

-- 2. expect `:=`, misuse `<-`
def oops₂ : IO String := do
  let io <- getIO "str"
  io -- type mismatch: expected `IO String`, got `String`

-- 3. in `if let`, expect `:=`, misuse `<-`
def oops₃ : IO String := do
  if let some opt <- getOpt "str" then  -- unexpected token '<-'; expected ':=' or '←'
    let ret := (<- getIO opt)
    return ret
  else
    return "none"

-- 4 in `if let`, expect := (<- ... )

-- 4.1 misuse `:=` gives me type mismatch

def oops₄₁ : IO String := do
  if let some opt := getOptIO "str" then -- type mismatch: expected `IO (Option String)`, got `Option ?m.3586`
    let ret <- getIO opt
    pure ret
  else
    pure "none"

-- 4.2 misues `<-`
def oops₄₂ : IO String := do
  if let some opt <- getOptIO "str" then -- unexpected token '<-'; expected ':=' or '←'
    let ret <- getIO opt
    pure ret
  else
    pure "none"

def works₄₃ : IO String := do
  if let some opt := (<- getOptIO "str") then
    let ret <- getIO opt
    pure ret
  else
    pure "none"


-- From https://github.com/leanprover/lean4/pull/2676

example : IO Unit := do
  let x ← if true then pure true else pure false

example : Id Unit := do
  let mut x ← if true then pure true else pure false
  if let .true := x then
    x := false