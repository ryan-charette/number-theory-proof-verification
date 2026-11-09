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

end NumberTheory.CoefficientTest
