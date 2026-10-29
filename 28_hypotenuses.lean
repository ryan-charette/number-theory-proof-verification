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

theorem primitive_hypotenuse_factors (a b c : Int) (h : Primitive a b c) :
    ∃ ps : List Nat, PrimeFactors ps ∧ product ps=c.natAbs ∧
      ∀ p ∈ ps, p%4=1 := by
  /-
  Theorem: A primitive triangle's hypotenuse is a product of primes
  congruent to one modulo four.
  Proof: Factor the positive hypotenuse. It is odd, so two is absent.
  If a prime factor had remainder three modulo four, its divisibility
  into c*c=a*a+b*b would force it to divide both legs. It would then
  be a common divisor of all three sides, contradicting primitivity.
  Every remaining prime has remainder one. QED
  -/
  have hc := h.1.2.2.1
  have hcast : (c.natAbs:Int)=c := Int.natAbs_of_nonneg (by omega)
  rcases NumberTheory.DivisibilityTests.positive_factorization c.natAbs (by omega) with ⟨ps,hps,he⟩
  refine ⟨ps,hps,he,?_⟩
  intro p hp
  have hprime := hps p hp
  have hperm := List.perm_cons_erase hp
  have hf := NumberTheory.Factorization.product_perm _ _ hperm
  rw [he] at hf
  have hdn : p ∣ c.natAbs := ⟨_,hf⟩
  have hd : (p:Int) ∣ c := Int.ofNat_dvd_left.mpr hdn
  have hp2 : p≠2 := by
    intro hh
    subst p
    have hodd := (NumberTheory.RightTriangles.primitive_parity a b c h).2
    omega
  rcases NumberTheory.PrimeBounds.prime_residue_mod_four p hprime hp2 with hh | hh
  · exact hh
  · have hsum : (p:Int) ∣ a*a+b*b := by
      rw [h.1.2.2.2]
      rcases hd with ⟨u,hu⟩
      exact ⟨u*c,by rw [hu,Int.mul_assoc]⟩
    have hab := NumberTheory.SquarePairs.prime_three_divides_roots p hprime hh a b hsum
    have hone := h.2 p (by have := hprime.1; omega) hab.1 hab.2 hd
    have := hprime.1
    omega

end NumberTheory.Hypotenuses
