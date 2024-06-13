import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

open Lean Json ToJson FromJson

def ex1 := json% { "a": 1, "b": 3.14, "c" : {
  "d": [1, 2, 3],
  "e": "hello",
  "g": [1, "x", 3.14] -- OK: this is in Json but not in Foo
}}

structure Bar where
  d : Array Nat
  e : String
  f : Option String -- OK: this is in Foo but not in Json
  deriving FromJson,ToJson,Repr

structure Foo where
  a : Nat
  b : Float
  c : Bar
  deriving FromJson,ToJson,Repr

def fromJsonStrFoo (str : String) : Option Foo :=
  if let .ok (f : Foo) := Json.parse str >>= fromJson? then
    some f
  else
    none

#eval fromJsonStrFoo ex1.pretty

def x := Json.parse ex1.pretty >>= @fromJson? Foo _

def y : Except String Foo := Json.parse ex1.pretty >>= fromJson?

def z : Option Foo :=
  if let .ok (f : Foo) := Json.parse ex1.pretty >>= fromJson? then some f else none

-- Following https://github.com/leanprover-community/llm/blob/main/scripts/runLinter.lean

def fromJsonStr (A) [FromJson A] (str : String) : IO A := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse str

def toJsonStr (A) [ToJson A] (a : A) : String :=
  toJson a |>.pretty
