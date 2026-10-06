import Init.Data.Nat.Dvd
import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Omega

/-
Elementary constructions of primes beyond a bound. All supporting
results are proved here, independently of the other source files.
-/

namespace NumberTheory.PrimeBounds


def Coprime (a b : Nat) : Prop := ∀ d : Nat, d ∣ a → d ∣ b → d = 1

theorem consecutive_coprime (n : Nat) : Coprime n (n+1) := by
  /-
  Theorem: Consecutive natural numbers are coprime.
  Proof: A common divisor d divides both n and n+1, so it divides
  their difference one. A natural divisor of one is one. Hence the
  only common divisor is one, which says their greatest common
  divisor is one. This formulation also includes n=0. QED

  We express coprimality directly by its common-divisor property;
  no library gcd is needed in this file.
  -/
  intro d hd hn
  have hdiv := Nat.dvd_sub (by omega : n ≤ n+1) hn hd
  have hone : d ∣ 1 := by
    rw [show n+1-n=1 by omega] at hdiv
    exact hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < 1) hone
  rcases hone with ⟨t, ht⟩
  have hne : d ≠ 0 := by intro hz; simp [hz] at ht
  omega



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

end NumberTheory.PrimeBounds
