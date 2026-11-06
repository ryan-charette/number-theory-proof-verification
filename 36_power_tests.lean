import «35_test_costs»

namespace NumberTheory.PowerTests

open NumberTheory.Factorization NumberTheory.PowerCycles NumberTheory.TestCosts

/-- Multiplications in recursive binary powering: square, then multiply for an odd bit. -/
def powerCount (r : Nat) : Nat :=
  if h : r=0 then 0 else powerCount (r/2)+1+r%2
termination_by r
decreasing_by omega

theorem binary_count_bound (k r : Nat) (hr : r<2^k) : powerCount r≤2*k := by
  /-
  Lemma: An exponent smaller than 2^k takes at most 2k multiplications
  in binary powering. For exponent zero none are needed. Otherwise,
  halve the exponent, square the resulting power, and multiply once
  more by the base when the exponent is odd. Each level adds at most
  two multiplications. Induction on k proves the bound, since halving
  an exponent below 2^(k+1) leaves one below 2^k. Reductions modulo
  the modulus keep the operands bounded and use no additional
  multiplications in this counting model. QED
  -/
  induction k generalizing r with
  | zero =>
    have hz : r=0 := by simp at hr; omega
    simp [hz,powerCount]
  | succ k ih =>
    by_cases hz : r=0
    · simp [hz,powerCount]
    · have ht : r/2<2^k := by
        rw [Nat.pow_succ] at hr
        omega
      have hi := ih (r/2) ht
      rw [powerCount,dif_neg hz]
      omega

end NumberTheory.PowerTests
