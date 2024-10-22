-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Force.20a.20Lean.20evaluation/near/338717704
def time (f : IO α) : IO (String × α) := do
  let pre ← IO.monoMsNow
  let ret ← f
  let post ← IO.monoMsNow
  let monoMs := post - pre
  let seconds := monoMs.toFloat / 1000.0
  let elapsed := s!"{seconds}s"
  pure (elapsed.replace "000s" "s", ret)
