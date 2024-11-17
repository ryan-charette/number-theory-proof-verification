import «Number Theory».Basic
import Mathlib.Tactic.NthRewrite

/-
  We now advance to proving implications, i.e., if-then statements. The main
  tool we use to prove statements of this type is the `exact`. Compared to
  `rfl` and `rw`, `exact` is very strict, and requires, as the name implies,
  that the input match the goal exactly.
-/

example (x y : Nat) (h1 : x + y = 37) : x + y = 37 := by
  /-
  Theorem: If x + y = 37, then x + y = 37.
  Proof: This is tautological; assume the hypothesis. Then

  x + y = 37

  QED
  -/
  exact h1

example (x : Nat) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  /-
  Theorem: If 0 + x = 0 + y + 2, then x = y + 2.
  Proof: Assume the hypothesis. Then

  0 + x = 0 + y + 2

  x = y + 2    [Zero is the additive identity]

  QED
  -/
  repeat rw [Nat.zero_add] at h
  exact h
