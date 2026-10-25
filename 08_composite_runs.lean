import «04_factorization»
import «06_prime_bounds»
import Init.Data.Nat.Dvd
import Lean.Elab.Tactic.Omega

namespace NumberTheory.CompositeRuns

open NumberTheory.PrimeBounds (divides_initialProduct initialProduct initialProduct_positive)
open NumberTheory.Factorization (Composite)


theorem initial_product_offset_composite (k d : Nat) (hd : 1 < d) (hle : d ≤ k) :
    Composite (initialProduct k+d) := by
  /-
  Lemma: If 2≤d≤k, adding d to the product of the integers from one
  through k gives a composite number.
  Proof: Write that product P as d*q, since d is one of its factors.
  Then P+d=d*(q+1). Positivity of P gives q>0, so both d and q+1
  exceed one. Moreover d<P+d because P>0, and q+1<d*(q+1) because
  d>1. Thus we have expressed P+d as a product of two smaller
  natural numbers, which is the definition of composite. QED
  -/
  have hP := initialProduct_positive k
  rcases divides_initialProduct d k (by omega) hle with ⟨q,hq⟩
  have he : initialProduct k+d = d*(q+1) := by
    rw [hq, Nat.mul_add, Nat.mul_one]
  have hqpos : 0 < q := by
    by_cases hz : q = 0
    · rw [hz, Nat.mul_zero] at hq
      omega
    · omega
  have hsmall := Nat.mul_lt_mul_of_pos_right hd (by omega : 0 < q+1)
  rw [Nat.one_mul, ← he] at hsmall
  exact ⟨d,q+1,by omega,hsmall,he⟩

theorem arbitrarily_long_composite_runs (n : Nat) :
    ∃ start length : Nat, 0 < start ∧ n < length ∧
      ∀ i : Nat, i < length → Composite (start+i) := by
  /-
  Theorem: For every natural number n, there is a run of more than
  n consecutive composite numbers.
  Proof: Let P be the product of the integers from one through n+2.
  Consider the consecutive numbers P+2,P+3,...,P+(n+2). There are
  n+1 of them, more than n. At position i, starting with position
  zero, the offset is d=i+2. Since 2≤d≤n+2, d divides P and the
  preceding lemma proves that P+d is composite. Thus every entry
  in the claimed run is composite. The construction also works for
  n=0, when a single composite number is enough. QED

  We describe a consecutive run by a positive starting number and
  its length; its entries are start+i for 0≤i<length.
  -/
  refine ⟨initialProduct (n+2)+2,n+1,by omega,by omega,?_⟩
  intro i hi
  have h := initial_product_offset_composite (n+2) (i+2) (by omega) (by omega)
  simpa only [Nat.add_assoc, Nat.add_comm i 2] using h

end NumberTheory.CompositeRuns
