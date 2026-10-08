import Init.Data.Nat.Dvd
import Lean.Elab.Tactic.Omega

namespace NumberTheory.CompositeRuns

def initialProduct : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * initialProduct n

theorem initialProduct_positive (n : Nat) : 0 < initialProduct n := by
  /-
  Lemma: The product of the integers from one through n is positive.
  Proof: The empty product is one. Each next product multiplies a
  positive preceding product by the positive integer n+1. Induction
  therefore proves positivity for every n. QED
  -/
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem divides_initialProduct (d n : Nat) (hd : 0 < d) (hle : d ≤ n) :
    d ∣ initialProduct n := by
  /-
  Lemma: Every positive integer at most n divides the product of the
  integers from one through n.
  Proof: Induct on n. There is no positive integer at most zero.
  At the next step, if d=n+1 it is the newly added factor. Otherwise
  d≤n, so write the preceding product as d*t by induction. The new
  product is then d*((n+1)*t), giving the required quotient. QED
  -/
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : d = n+1
    · subst d
      exact ⟨initialProduct n, rfl⟩
    · rcases ih (by omega) with ⟨t, ht⟩
      exists (n+1)*t
      rw [initialProduct, ht]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

end NumberTheory.CompositeRuns
