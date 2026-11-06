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

theorem decimal_power_count (r d : Nat) (hd : DecimalDigits r d) :
    powerCount r≤8*d := by
  /-
  Theorem: Binary powering of a d-digit exponent takes at most 8d
  multiplications, so its multiplication count is polynomial in d.
  Proof: A d-digit exponent is below 10^d. Since 10<=16=2^4,
  it is also below 2^(4d). Apply the binary bound with k=4d.
  This counts multiplications for a fixed modulus. Bit costs depend
  additionally on the modulus size. QED
  -/
  have hten : 10^d≤16^d := Nat.pow_le_pow_left (by decide) d
  have hpow : 16^d=2^(4*d) := by rw [Nat.pow_mul]
  have hr : r<2^(4*d) := by
    rw [← hpow]
    exact Nat.lt_of_lt_of_le hd.2.2 hten
  have hh := binary_count_bound (4*d) r hr
  omega
end NumberTheory.PowerTests
