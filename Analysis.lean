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

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, ih]

theorem succ_add (n m : Nat) : n.succ + m = (n + m).succ := by
  induction m with
  | zero =>
    repeat rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, ih, Nat.add_succ]

theorem add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero =>
    rw [Nat.add_zero, Nat.zero_add]
  | succ d ih =>
    rw [← Nat.succ_eq_add_one, Nat.add_succ, Nat.succ_add, ih]

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
    repeat rw [Nat.zero_add]
  | succ d ih =>
    rw [← Nat.succ_eq_add_one]
    repeat rw [Nat.succ_add]
    rw [ih]

theorem add_cancel {a b c : Nat} (h : a + b = a + c) : b = c := by
  induction a with
  | zero =>
    repeat rw [Nat.zero_add] at h
    exact h
  | succ d ih =>
    rw [← Nat.succ_eq_add_one, Nat.succ_add, Nat.succ_add, Nat.succ_inj'] at h
    apply ih
    exact h

theorem add_pos {a b : Nat} (h: a ≠ 0) : (a + b) ≠ 0 := by
  induction b with
  | zero =>
    rw [Nat.add_zero]
    exact h
  | succ d =>
    rw [Nat.add_succ]
    exact Nat.succ_ne_zero (a + d)

