import «35_test_costs»
import Mathlib.Tactic.NormNum

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
theorem failed_power_not_prime (n a : Nat) (ha : 0<a) (han : a<n)
    (hfail : ¬ Congruent ((a:Int)^(n-1)) 1 n) : ¬ Prime n := by
  /-
  Theorem: A positive base below n whose predecessor power is not
  congruent to one proves that n is not prime. Proof: If n were prime,
  the earlier coprimality lemma would make a coprime to n. Fermat's
  theorem would then give exactly the congruence assumed to fail.
  This contradiction proves the contrapositive. The positive-base
  condition excludes zero, which fails the test even for primes. QED
  -/
  intro hp
  exact hfail (fermat_coprime a n hp (small_prime_coprime n a hp ha han))
theorem composite_737 : ¬ Prime 737 := by
  /-
  Theorem: The integer 737 is composite. Proof: The base two lies
  strictly between zero and 737. Repeated squaring and reduction
  give 2^736 congruent to 86 modulo 737, rather than one. The
  contrapositive of Fermat's theorem therefore excludes primality.
  Lean checks the finite integer calculation, while the earlier
  theorem supplies the implication from failed congruence. QED
  -/
  apply failed_power_not_prime 737 2 (by decide) (by decide)
  norm_num [Congruent]
theorem prime_iff_all_bases (n : Nat) (hn : 1<n) :
    Prime n ↔ ∀ a : Nat, 0<a → a<n → Congruent ((a:Int)^(n-1)) 1 n := by
  /-
  Theorem: For n>1, primality is equivalent to every positive base
  below n having its (n-1)st power congruent to one modulo n.
  Proof: The forward direction is Fermat's theorem, using the earlier
  coprimality result. Conversely, suppose n is composite and write
  n=a*b with 1<a<n. The proposed test applies to a. Since n-1>0,
  a divides a^(n-1). Also a divides n, and the congruence implies
  n divides a^(n-1)-1. Hence a divides both that power and that power
  minus one, so it divides their difference, one. A positive divisor
  of one is at most one, contradicting a>1. QED

  The base range is explicitly 1<=a<n. Including a=0 would make
  the statement false for every prime. The exponent is positive
  because n>1. The argument tests all bases, including noncoprime ones.
  -/
  constructor
  · intro hp a ha han
    exact fermat_coprime a n hp (small_prime_coprime n a hp ha han)
  · intro hall
    apply Classical.byContradiction
    intro hnp
    obtain ⟨a,b,ha,han,_,_,hab⟩ := nonprime_factors n hn hnp
    have htest := hall a (by omega) han
    have hdiv : (a:Int)∣(n:Int) := ⟨b,by rw [hab,Int.natCast_mul]⟩
    have he : n-1=(n-2)+1 := by omega
    have hpower : (a:Int)∣(a:Int)^(n-1) := by
      refine ⟨(a:Int)^(n-2),?_⟩
      rw [he,Int.pow_succ,Int.mul_comm]
    have hminus : (a:Int)∣(a:Int)^(n-1)-1 :=
      NumberTheory.dvd_trans _ _ _ hdiv htest.2
    have hone := NumberTheory.dvd_sub (a:Int) ((a:Int)^(n-1))
      ((a:Int)^(n-1)-1) hpower hminus
    have hid : (a:Int)^(n-1)-((a:Int)^(n-1)-1)=1 := by omega
    rw [hid] at hone
    have hle := NumberTheory.CommonDivisors.divisor_le_positive (a:Int) 1 (by decide) hone
    omega

end NumberTheory.PowerTests
