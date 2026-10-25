import «01_divisibility»
import «04_factorization»
import «12_modular_powers»
import «13_power_cycles»
import «18_order_counts»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PrimitiveTests

open NumberTheory (Congruent)
open NumberTheory.Factorization (Prime)
open NumberTheory.PowerCycles (fermat_coprime order_dvd_iff prime_coprime)
open NumberTheory.ModularPowers (order order_spec)
open NumberTheory.OrderCounts (PrimitiveRoot)


theorem prime_order_divides (a : Int) (p : Nat) (hp : Prime p)
    (ha : ¬ (p : Int) ∣ a) : order a p ∣ p-1 := by
  /-
  Theorem: The order of an integer not divisible by a prime p
  divides p-1.
  Proof: Such an integer is coprime to p. Fermat's theorem says
  that its (p-1)st power is congruent to one. The order divides
  every exponent with that property, so it divides p-1. QED
  -/
  have hc := prime_coprime a p hp ha
  exact (order_dvd_iff a p (by have := hp.1; omega) hc (p-1)).mp
    (fermat_coprime a p hp hc)

theorem primitive_root_test (a : Int) (p : Nat) (hp : Prime p)
    (ha : ¬ (p : Int) ∣ a) :
    PrimitiveRoot a p ↔ ∀ f : Nat, 1 < f → f ∣ p-1 →
      ¬ Congruent (a^((p-1)/f)) 1 p := by
  /-
  Theorem: For a prime p and an integer a not divisible by p,
  a is a primitive root exactly when a^((p-1)/f) is not congruent
  to one for every divisor f>1 of p-1.
  Proof: Put d=order(a,p). It is positive and divides p-1.
  If a is a primitive root, d=p-1. Dividing p-1 by f>1 gives
  a smaller exponent, so it cannot be a positive multiple of d.
  It is positive because f divides the positive integer p-1.
  Thus its power cannot be congruent to one.

  Conversely, write p-1=d*f. Since p-1 is positive, f is positive.
  If f>1, it is a divisor tested by the hypothesis. But
  (p-1)/f=d, and a^d is congruent to one, a contradiction.
  Therefore f=1 and d=p-1, which makes a a primitive root. QED

  The test excludes f=1 and explicitly assumes p does not divide
  a. These are the approved corrections to the stated criterion.
  The case p=2 is included: there are no divisors f>1 to test.
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hm : 0 < p-1 := by have := hp.1; omega
  have hc := prime_coprime a p hp ha
  have hs := order_spec a p hn hc
  constructor
  · intro hroot f hf hdiv hpower
    have hd := (order_dvd_iff a p hn hc ((p-1)/f)).mp hpower
    rw [hroot.2] at hd
    have ht : 0 < (p-1)/f := by
      rcases hdiv with ⟨t,ht⟩
      have hpos : 0 < t := by
        by_cases hz : t=0
        · simp [hz] at ht
          omega
        · omega
      rw [ht,Nat.mul_div_cancel_left t (by omega)]
      exact hpos
    have hle := Nat.le_of_dvd ht hd
    have hlt := Nat.div_lt_self hm hf
    omega
  · intro htest
    rcases prime_order_divides a p hp ha with ⟨f,hf⟩
    have hfpos : 0 < f := by
      by_cases hz : f=0
      · simp [hz] at hf
        omega
      · omega
    have hone : f=1 := by
      apply Classical.byContradiction
      intro hne
      have hbig : 1 < f := by omega
      have hdiv : f ∣ p-1 := ⟨order a p,by rw [hf,Nat.mul_comm]⟩
      have he : (p-1)/f=order a p := by
        rw [hf,Nat.mul_div_cancel _ hfpos]
      apply htest f hbig hdiv
      rw [he]
      exact hs.2.1
    exact ⟨hc,by simpa [hone] using hf.symm⟩

end NumberTheory.PrimitiveTests
