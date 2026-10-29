import «27_square_pairs»

namespace NumberTheory.Hypotenuses

open NumberTheory.CommonDivisors
open NumberTheory.Factorization (Prime PrimeFactors product)
open NumberTheory.DivisibilityTests (prime_2 prime_dvd_integer_product)
open NumberTheory.RightTriangles (Primitive)

/- A product in the converse is nonempty: the empty product one cannot
be a hypotenuse of a triple with positive legs. -/

theorem coprime_prime_test (a b : Int) :
    gcd a b=1 ↔ ∀ p : Nat, Prime p → ¬ ((p:Int) ∣ a ∧ (p:Int) ∣ b) := by
  /-
  Lemma: Two integers are coprime exactly when no prime divides both.
  Proof: A common prime divisor divides every linear combination,
  so a Bezout combination equal to one rules it out. Conversely,
  a gcd greater than one has a prime divisor, which divides both
  inputs. A zero gcd makes both inputs zero, so two divides both.
  The only remaining nonnegative gcd is one. QED
  -/
  constructor
  · intro hc p hp hd
    rcases coprime_bezout a b hc with ⟨u,v,huv⟩
    have hh := dvd_linear p a b u v hd.1 hd.2
    rw [huv] at hh
    have := divisor_le_positive p 1 (by decide) hh
    have := hp.1
    omega
  · intro hn
    have hg := gcd_data a b
    by_cases hz : gcd a b=0
    · have ha : a=0 := by rcases hg.2.1 with ⟨u,hu⟩; rw [hz,Int.zero_mul] at hu; exact hu
      have hb : b=0 := by rcases hg.2.2.1 with ⟨v,hv⟩; rw [hz,Int.zero_mul] at hv; exact hv
      exact False.elim (hn 2 prime_2 ⟨ha ▸ dvd_zero 2,hb ▸ dvd_zero 2⟩)
    · by_cases ho : gcd a b=1
      · exact ho
      · have habs := Int.natAbs_of_nonneg hg.1
        have hpos : 1<(gcd a b).natAbs := by omega
        rcases NumberTheory.Factorization.prime_divisor _ hpos with ⟨p,hp,hd⟩
        have hdi : (p:Int) ∣ gcd a b := Int.ofNat_dvd_left.mpr hd
        exact False.elim (hn p hp ⟨Int.dvd_trans hdi hg.2.1,Int.dvd_trans hdi hg.2.2.1⟩)

end NumberTheory.Hypotenuses
