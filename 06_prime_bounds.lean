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


theorem avoids_small_divisors (k : Nat) :
    ∃ n : Nat, 1 < n ∧ ∀ d : Nat, 1 < d → d ≤ k → ¬ d ∣ n := by
  /-
  Theorem: For any bound k, there is a number greater than one with
  no divisor between two and k, inclusive.
  Proof: Let P be the product of the integers from one through k,
  and take n=P+1. Positivity of P gives n>1. Every d between two
  and k divides P. If it also divided P+1, coprimality of these
  consecutive integers would force d=1, a contradiction. QED

  The inclusive upper bound strengthens the version with d<k.
  -/
  exists initialProduct k + 1
  constructor
  · have := initialProduct_positive k
    omega
  · intro d hd hle hdiv
    have he := consecutive_coprime (initialProduct k) d
      (divides_initialProduct d k (by omega) hle) hdiv
    omega

def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem nonprime_factors (n : Nat) (hn : 1 < n) (hp : ¬ Prime n) :
    ∃ a b : Nat, 1 < a ∧ a < n ∧ 1 < b ∧ b < n ∧ n = a * b := by
  /-
  Theorem: A nonprime number greater than one is a product of two
  numbers strictly between one and itself.
  Proof: Since n is not prime, it has a divisor a other than one and n.
  Write n=a*b. Neither factor is zero. The factor b cannot be one,
  since that would give a=n. Both factors are therefore at least two.
  Each divides n and is at most n; equality would force the other
  factor to be one. Thus both factors are strictly smaller than n. QED
  -/
  have hex : ∃ a : Nat, a ∣ n ∧ a ≠ 1 ∧ a ≠ n := by
    apply Classical.byContradiction
    intro he
    apply hp
    constructor
    · exact hn
    · intro a ha
      by_cases h₁ : a = 1
      · exact Or.inl h₁
      · by_cases h₂ : a = n
        · exact Or.inr h₂
        · exact False.elim (he ⟨a, ha, h₁, h₂⟩)
  rcases hex with ⟨a, ha, ha₁, han⟩
  rcases ha with ⟨b, heq⟩
  have ha₀ : a ≠ 0 := by intro hz; rw [hz, Nat.zero_mul] at heq; omega
  have hb₀ : b ≠ 0 := by intro hz; rw [hz, Nat.mul_zero] at heq; omega
  have hb₁ : b ≠ 1 := by intro ho; rw [ho, Nat.mul_one] at heq; omega
  have hal := Nat.le_of_dvd (by omega : 0 < n) (show a ∣ n from ⟨b, heq⟩)
  have hbl := Nat.le_of_dvd (by omega : 0 < n) (show b ∣ n from ⟨a, by rw [Nat.mul_comm]; exact heq⟩)
  have hbn : b ≠ n := by
    intro hbn
    have ht : b * a = b * 1 := by rw [Nat.mul_one, Nat.mul_comm]; omega
    have haeq := Nat.eq_of_mul_eq_mul_left (by omega : 0 < b) ht
    exact ha₁ haeq
  exists a, b
  exact ⟨by omega, by omega, by omega, by omega, heq⟩

end NumberTheory.PrimeBounds
