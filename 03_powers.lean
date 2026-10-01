import «02_congruence»

namespace NumberTheory

theorem modeq_square (a b n : Int) (h : a ≡ b [MOD n]) :
    a ^ 2 ≡ b ^ 2 [MOD n] := by
  /-
  Exercise 1.15: Squaring preserves congruence.
  Proof: Multiply the given congruence by itself. QED
  -/
  have h₂ := modeq_mult a b a b n h h
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul,
    Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  exact h₂

theorem modeq_cube (a b n : Int) (h : a ≡ b [MOD n]) :
    a ^ 3 ≡ b ^ 3 [MOD n] := by
  /-
  Exercise 1.16: Cubing preserves congruence.
  Proof: Multiply the congruence of the squares by the original one. QED
  -/
  rw [Int.pow_succ, Int.pow_succ b]
  exact modeq_mult (a ^ 2) (b ^ 2) a b n (modeq_square a b n h) h

theorem modeq_pow_step (a b n : Int) (k : Nat)
    (h : a ≡ b [MOD n]) (hk : a ^ k ≡ b ^ k [MOD n]) :
    a ^ (k + 1) ≡ b ^ (k + 1) [MOD n] := by
  /-
  Exercise 1.17: Advance an exponent by one.
  Proof: a ^ (k + 1) = a ^ k * a, and likewise for b.
  Multiply the two assumed congruences. QED
  -/
  rw [Int.pow_succ, Int.pow_succ]
  exact modeq_mult (a ^ k) (b ^ k) a b n hk h

theorem modeq_pow (a b n : Int) (k : Nat) (h : a ≡ b [MOD n]) :
    a ^ k ≡ b ^ k [MOD n] := by
  /-
  Theorem 1.18: Every natural-number power preserves congruence.
  Proof: We use induction on k, including zero.

  Base case: Both powers are 1, so reflexivity applies.
  Inductive case: Multiply the congruence for exponent k by a ≡ b.

  QED
  -/
  induction k with
  | zero =>
    rw [Int.pow_zero, Int.pow_zero]
    exact modeq_refl 1 n h.1
  | succ k ih =>
    exact modeq_pow_step a b n k h ih

end NumberTheory
