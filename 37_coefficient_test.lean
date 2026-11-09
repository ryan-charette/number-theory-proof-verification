import «14_binomial_powers»
import Mathlib.Tactic.Ring

namespace NumberTheory.CoefficientTest

open NumberTheory.BinomialPowers NumberTheory.Factorization
open NumberTheory.CommonDivisors NumberTheory.ModularPowers

theorem weighted_coefficient (m j : Nat) (hj : j≤m) :
    ((j+1:Nat):Int)*coefficient (m+1) (j+1) =
    ((m+1:Nat):Int)*coefficient m j := by
  /-
  Multiply both sides by j! (m-j)!. On the left, (j+1)j! is
  (j+1)!, so the factorial formula gives (m+1)!. On the right,
  the same formula gives (m+1)m!, also (m+1)!. The factor we
  introduced is positive, so cancellation proves the identity. QED
  -/
  have hleft := coefficient_factorial (m+1) (j+1) (by omega)
  rw [show m+1-(j+1)=m-j by omega] at hleft
  have hright := coefficient_factorial m j hj
  apply Int.eq_of_mul_eq_mul_left (ne_of_gt (Int.mul_pos (factorial_positive j)
    (factorial_positive (m-j))))
  calc
    _ = coefficient (m+1) (j+1)*(((j+1:Nat):Int)*factorial j)*factorial (m-j) := by ring
    _ = ((m+1:Nat):Int)*factorial m := hleft
    _ = _ := by rw [← hright]; ring

theorem prime_of_interior_divisibility (n : Nat) (hn : 1<n)
    (hall : ∀ i : Nat, 0<i → i<n → (n:Int) ∣ coefficient n i) : Prime n := by
  /-
  Suppose n has a factor d strictly between one and n. In row n-1,
  the first coefficient is one, so d does not divide it. Each pair
  of consecutive entries in that row sums to an interior entry of
  row n. The sum is divisible by n and hence by d. If d divided the
  next entry, subtraction would show it divided the previous one.
  Thus d does not divide any entry through position d-1.

  On the other hand, write C(n,d)=n*q. The weighted coefficient
  identity gives d*n*q=n*C(n-1,d-1). Cancelling n gives exactly
  the divisibility we just ruled out. Hence n must be prime. QED
  -/
  apply Classical.byContradiction
  intro hnp
  obtain ⟨d,b,hd,hdn,_,_,hnprod⟩ := nonprime_factors n hn hnp
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  let D : Int := (j+1:Nat)
  let N : Int := (m+1:Nat)
  have hdvd : D∣N := ⟨b,by dsimp [N,D]; exact_mod_cast hnprod⟩
  have avoids (i : Nat) (hi : i<m+1) : ¬ D∣coefficient m i := by
    induction i with
    | zero =>
      rw [(coefficient_edges m).1]
      intro h
      have hle := divisor_le_positive D 1 (by decide) h
      dsimp [D] at hle
      omega
    | succ i ih =>
      intro hnext
      have hsum := NumberTheory.dvd_trans _ _ _ hdvd (hall (i+1) (by omega) hi)
      change D∣coefficient m i+coefficient m (i+1) at hsum
      have hdiff := NumberTheory.dvd_sub _ _ _ hsum hnext
      exact ih (by omega) (by simpa using hdiff)
  obtain ⟨q,hq⟩ := hall (j+1) (by omega) hdn
  have he := weighted_coefficient m j (by omega)
  rw [hq] at he
  have heq : N*coefficient m j=N*(D*q) := by
    calc
      _ = D*(N*q) := he.symm
      _ = _ := by ring
  have hNpos : (0:Int)<N := by dsimp [N]; omega
  exact avoids j (by omega) ⟨q,Int.eq_of_mul_eq_mul_left (ne_of_gt hNpos) heq⟩

/-- At degree i, compare the binomial expansion of (X+a)^n with X^n+a.
The test is used for n greater than one, so the two terms on the right
have distinct degrees. -/
def CoefficientsAgree (n a : Nat) : Prop :=
  ∀ i : Nat, Congruent (coefficient n i * (a:Int)^(n-i))
    (if i=0 then (a:Int) else if i=n then 1 else 0) n

theorem prime_iff_coefficients_agree (n a : Nat) (hn : 1<n)
    (hcop : gcd (a:Int) n=1) : Prime n ↔ CoefficientsAgree n a := by
  /-
  If n is prime, Fermat's theorem gives the constant-term congruence.
  At every interior degree the binomial coefficient is divisible by n,
  so multiplying it by a power of a preserves divisibility. The leading
  coefficients are both one, and all higher coefficients vanish.

  Conversely, suppose the coefficients agree. At each interior degree
  i the right side has coefficient zero. The power of a in the left
  coefficient is relatively prime to n, so we can cancel it. Thus n
  divides every interior binomial coefficient, which forces n to be
  prime by the preceding result. QED
  -/
  have hpos : (0:Int)<n := by omega
  constructor
  · intro hp i
    by_cases hz : i=0
    · subst i
      simpa [(coefficient_edges n).1] using fermat_natural a n hp
    by_cases he : i=n
    · subst i
      simp [hz, (coefficient_edges n).2, Congruent, hpos]
    by_cases hi : i<n
    · obtain ⟨k,hk⟩ := prime_divides_coefficient n i hp (by omega) hi
      simp only [if_neg hz, if_neg he, Congruent, Int.sub_zero]
      exact ⟨hpos,k*(a:Int)^(n-i),by rw [hk]; ring⟩
    · simp [hz, he, coefficient_outside n i (by omega), Congruent, hpos]
  · intro hall
    apply prime_of_interior_divisibility n hn
    intro i hi hin
    have h := hall i
    simp only [if_neg (by omega : i≠0), if_neg (by omega : i≠n)] at h
    have hpower := coprime_power (a:Int) n hpos hcop (n-i)
    have hcancel := cancel_coprime (coefficient n i) 0 ((a:Int)^(n-i)) n
      hpower (by simpa using h)
    simpa using hcancel.2


end NumberTheory.CoefficientTest
