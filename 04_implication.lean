import «Number Theory».Basic

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
