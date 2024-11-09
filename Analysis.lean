-- This module serves as the root of the `«Number Theory»` library.
-- Import modules here that should be built as part of the library.
import «Number Theory».Basic
import Mathlib.Tactic.NthRewrite

/-
Peano's Axiom of Arithmetic:
  (1) 0 ∈ ℕ
  (2) If n ∈ ℕ, then S(n) ∈ ℕ
  (3) If n ∈ ℕ, then S(n) ≠ 0
  (4) If n, m ∈ ℕ and n ≠ m, then S(n) ≠ S(m)
  (5) If P(0) and P(k) → P(k + 1), then ∀ n ∈ ℕ P(n)
-/

/-
Definition of Addition:
  (1) Nat.add_zero (n : Nat) : 0 + n = n
  (2) Nat.add_succ (n m : Nat) : n + m.succ = (n + m).succ
-/
