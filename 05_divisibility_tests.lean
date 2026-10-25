import «03_common_divisors»
import «04_factorization»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.List.Perm
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Lean.Elab.Tactic.Omega

/-
This file develops applications of prime factors to divisibility and
integer equations. Earlier arithmetic and factorization results are imported, while new
supporting arguments are proved here.
-/

namespace NumberTheory.DivisibilityTests

open NumberTheory.CommonDivisors (coprime_bezout coprime_dvd_cancel coprime_of_bezout coprime_product coprime_product_dvd coprime_swap divisor_le_positive dvd_linear dvd_refl gcd gcd_data gcd_eq_of_combination)
open NumberTheory.Factorization (Prime PrimeFactors factorization_exists factorization_multiplicities prime_trial_bound product product_append product_perm)


theorem prime_product_positive (ps : List Nat) (hps : PrimeFactors ps) : 0 < product ps := by
  /-
  Lemma: A product of primes is positive, including the empty product.
  Proof: The empty product is one. For a nonempty list, the first
  prime is positive and the tail product is positive by induction.
  Multiplying two positive numbers gives a positive number. QED
  -/
  induction ps with
  | nil => decide
  | cons p ps ih =>
    exact Nat.mul_pos (by have := (hps p (by simp)).1; omega)
      (ih (fun q hq => hps q (by simp [hq])))

theorem positive_factorization (n : Nat) (hn : 0 < n) :
    ∃ ps : List Nat, PrimeFactors ps ∧ product ps = n := by
  /-
  Lemma: Every positive natural number has a prime product expression.
  Proof: For one, use the empty list, whose product is one. Any other
  positive number exceeds one, so factorization existence applies. QED
  -/
  by_cases h : n = 1
  · subst n
    exact ⟨[], (by intro p hp; cases hp), rfl⟩
  · exact factorization_exists n (by omega)

theorem product_dvd_of_counts (xs ys : List Nat)
    (h : ∀ p, xs.count p ≤ ys.count p) : product xs ∣ product ys := by
  /-
  Lemma: If each factor occurs at least as often in the second list,
  the first product divides the second.
  Proof: Induct on the first list. One divides every product. Otherwise
  its first factor p occurs in the second list. Remove one occurrence
  there. The count inequalities still hold for the two remaining lists.
  Induction supplies a quotient; restoring p gives the same quotient
  for the original products. QED
  -/
  induction xs generalizing ys with
  | nil => exact ⟨product ys, by simp [product]⟩
  | cons p ps ih =>
    have hmem : p ∈ ys := List.count_pos_iff_mem.mp (by have := h p; simp at this; omega)
    let zs := @List.erase Nat instBEqOfDecidableEq ys p
    have hperm : List.Perm ys (p :: zs) := List.perm_cons_erase hmem
    have hc (q : Nat) := hperm.countP_eq (fun t => t == q)
    have htail : ∀ q, ps.count q ≤ zs.count q := by
      intro q
      have hh := h q
      have he := hc q
      change ys.count q = (p :: zs).count q at he
      by_cases hq : q = p
      · subst q
        simp only [List.count_cons_self] at hh he
        omega
      · simp only [List.count_cons_of_ne hq] at hh he
        omega
    rcases ih zs htail with ⟨k, hk⟩
    exists k
    have he := product_perm ys (p :: zs) hperm
    change product ys = (p * product ps) * k
    rw [he, product, hk, Nat.mul_assoc]

theorem prime_product_dvd_iff (xs ys : List Nat)
    (hx : PrimeFactors xs) (hy : PrimeFactors ys) :
    product xs ∣ product ys ↔ ∀ p, xs.count p ≤ ys.count p := by
  /-
  Theorem: One positive integer divides another exactly when every
  prime exponent in its factorization is at most the corresponding
  exponent in the other factorization. Missing primes have exponent zero.
  Proof: If the second product is the first times k, positivity makes
  k positive. Factor k and concatenate its factors with the first list.
  Uniqueness of factorization says that this concatenation and the second
  list have the same counts. Thus each second count is the first count
  plus a nonnegative count. Conversely, remove the first list's factors
  one at a time from the second; the count inequalities ensure that all
  of them can be removed. The leftover product is the quotient. QED
  -/
  constructor
  · rintro ⟨k, hk⟩
    have hpos := prime_product_positive ys hy
    have hkpos : 0 < k := by
      by_cases hz : k = 0
      · simp [hz] at hk
        omega
      · omega
    rcases positive_factorization k hkpos with ⟨ks, hks, he⟩
    have hcat : PrimeFactors (xs ++ ks) := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hx p hp
      · exact hks p hp
    have hp := factorization_multiplicities (xs ++ ks) ys hcat hy
      (by rw [product_append, he, ← hk])
    intro p
    have hc := (hp.2 p).2
    rw [List.count_append] at hc
    omega
  · exact product_dvd_of_counts xs ys

noncomputable def factors (n : Nat) : List Nat :=
  if h : 0 < n then Classical.choose (positive_factorization n h) else []

noncomputable def exponent (p n : Nat) : Nat := (factors n).count p

theorem factors_spec (n : Nat) (hn : 0 < n) :
    PrimeFactors (factors n) ∧ product (factors n) = n := by
  /-
  Lemma: The chosen factor list of a positive number consists of primes
  and has that number as its product.
  Proof: Choose one of the lists supplied by existence. Its two defining
  properties hold by that existence proof. The choice of order will not
  affect any exponent, since uniqueness preserves occurrence counts.
  We use an empty list at zero only to make the definitions total;
  all statements about these exponents assume positive inputs. QED
  -/
  unfold factors
  rw [dif_pos hn]
  exact Classical.choose_spec (positive_factorization n hn)

theorem exponent_of_factors (n p : Nat) (hn : 0 < n)
    (ps : List Nat) (hps : PrimeFactors ps) (he : product ps = n) :
    exponent p n = ps.count p := by
  /-
  Lemma: Any prime factorization computes the same exponent.
  Proof: The chosen list and the supplied list have the same product.
  Uniqueness therefore gives the same number of occurrences of p. QED
  -/
  have hs := factors_spec n hn
  exact ((factorization_multiplicities (factors n) ps hs.1 hps
    (hs.2.trans he.symm)).2 p).2

theorem exponent_mul (p a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    exponent p (a * b) = exponent p a + exponent p b := by
  /-
  Lemma: Multiplication adds prime exponents.
  Proof: Concatenate prime lists for a and b. Its product is a*b, and
  its count of p is the sum of the two counts. Independence of the
  chosen factorization gives the asserted equality. QED
  -/
  have hfa := factors_spec a ha
  have hfb := factors_spec b hb
  have hcat : PrimeFactors (factors a ++ factors b) := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hfa.1 q hq
    · exact hfb.1 q hq
  rw [exponent_of_factors (a*b) p (Nat.mul_pos ha hb)
    (factors a ++ factors b) hcat (by rw [product_append, hfa.2, hfb.2])]
  exact List.count_append _ _ _

theorem exponent_pow (p a k : Nat) (ha : 0 < a) :
    exponent p (a ^ k) = k * exponent p a := by
  /-
  Lemma: Raising a positive number to the kth power multiplies every
  prime exponent by k. Proof: Induct on k. For k=0 the number is one,
  whose empty factorization has no primes. Each following power is
  the preceding power times a, so add one more copy of its exponent.
  QED
  -/
  induction k with
  | zero =>
    have he := exponent_of_factors 1 p (by decide) []
      (by intro q hq; cases hq) rfl
    simpa using he
  | succ k ih =>
    rw [Nat.pow_succ, exponent_mul p (a^k) a (Nat.pow_pos ha) ha, ih]
    rw [Nat.succ_mul]

theorem dvd_iff_exponents (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a ∣ b ↔ ∀ p, exponent p a ≤ exponent p b := by
  /-
  Theorem: A positive number divides another exactly when all its
  prime exponents are bounded by those of the other number.
  Proof: Apply the count criterion to chosen prime lists. Their
  products are the original numbers and their counts are the exponents.
  Nonprime indices have zero counts and impose no extra restriction. QED
  -/
  have hfa := factors_spec a ha
  have hfb := factors_spec b hb
  have h := prime_product_dvd_iff (factors a) (factors b) hfa.1 hfb.1
  rw [hfa.2, hfb.2] at h
  exact h

theorem dvd_of_square_dvd (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 ∣ b ^ 2) : a ∣ b := by
  /-
  Theorem: If the square of a positive number divides the square of
  another, the first number divides the second.
  Proof: The exponent criterion applied to the squares says that
  twice each exponent of a is at most twice its exponent in b.
  Cancel two from these inequalities and apply the criterion again.
  QED
  -/
  apply (dvd_iff_exponents a b ha hb).mpr
  intro p
  have he := (dvd_iff_exponents (a^2) (b^2) (Nat.pow_pos ha) (Nat.pow_pos hb)).mp h p
  rw [exponent_pow p a 2 ha, exponent_pow p b 2 hb] at he
  omega

theorem prime_2 : Prime 2 := by
  /-
  Lemma: 2 is prime. Proof: A nonprime number has a prime divisor
  whose square does not exceed it. Such a divisor is at least two.
  For two or three this square is already too large; for seven the
  only remaining possibility is two, which does not divide seven.
  Thus the trial-division criterion proves primality. QED
  -/
  apply (prime_trial_bound 2 (by decide)).mpr
  intro q hq hbound hd
  have hqpos := hq.1
  have hfour := Nat.mul_le_mul (by omega : 2 ≤ q) (by omega : 2 ≤ q)
  omega

theorem prime_3 : Prime 3 := by
  /-
  Lemma: 3 is prime. Proof: A nonprime number has a prime divisor
  whose square does not exceed it. Such a divisor is at least two.
  For two or three this square is already too large; for seven the
  only remaining possibility is two, which does not divide seven.
  Thus the trial-division criterion proves primality. QED
  -/
  apply (prime_trial_bound 3 (by decide)).mpr
  intro q hq hbound hd
  have hqpos := hq.1
  have hfour := Nat.mul_le_mul (by omega : 2 ≤ q) (by omega : 2 ≤ q)
  omega

theorem prime_7 : Prime 7 := by
  /-
  Lemma: 7 is prime. Proof: A nonprime number has a prime divisor
  whose square does not exceed it. Such a divisor is at least two.
  For two or three this square is already too large; for seven the
  only remaining possibility is two, which does not divide seven.
  Thus the trial-division criterion proves primality. QED
  -/
  apply (prime_trial_bound 7 (by decide)).mpr
  intro q hq hbound hd
  have hqpos := hq.1
  have hsmall : q < 3 := by
    apply Classical.byContradiction
    intro h
    have hnine := Nat.mul_le_mul (by omega : 3 ≤ q) (by omega : 3 ≤ q)
    omega
  have he : q = 2 := by omega
  rcases hd with ⟨t, ht⟩
  rw [he] at ht
  omega

theorem exponent_7_7 : exponent 7 7 = 1 := by
  /-
  Lemma: The exponent of 7 in 7 is one.
  Proof: The prime factor list [7] has product 7. Counting the
  entries equal to 7 gives one; uniqueness makes this the exponent.
  QED
  -/
  rw [exponent_of_factors 7 7 (by decide) [7]]
  · decide
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq
    subst q
    exact prime_7
  · decide

theorem exponent_3_12 : exponent 3 12 = 1 := by
  /-
  Lemma: The exponent of 3 in 12 is one.
  Proof: The prime factor list [2, 2, 3] has product 12. Counting the
  entries equal to 3 gives one; uniqueness makes this the exponent.
  QED
  -/
  rw [exponent_of_factors 12 3 (by decide) [2, 2, 3]]
  · decide
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq
    · subst q
      exact prime_2
    · subst q
      exact prime_2
    · subst q
      exact prime_3
  · decide

theorem exponent_3_24 : exponent 3 24 = 1 := by
  /-
  Lemma: The exponent of 3 in 24 is one.
  Proof: The prime factor list [2, 2, 2, 3] has product 24. Counting the
  entries equal to 3 gives one; uniqueness makes this the exponent.
  QED
  -/
  rw [exponent_of_factors 24 3 (by decide) [2, 2, 2, 3]]
  · decide
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq | hq
    · subst q
      exact prime_2
    · subst q
      exact prime_2
    · subst q
      exact prime_2
    · subst q
      exact prime_3
  · decide

theorem power_equation_obstruction (p c k m n : Nat)
    (hc : 0 < c) (hm : 0 < m) (hn : 0 < n)
    (hnot : ¬ k ∣ exponent p c) : c * m ^ k ≠ n ^ k := by
  /-
  Lemma: If some prime exponent in c is not divisible by k, the
  equation c*m^k=n^k has no positive integer solutions.
  Proof: Comparing that exponent gives e(c)+k*e(m)=k*e(n).
  Both k*e(m) and the right side are divisible by k. Subtracting the
  former from the latter shows k divides e(c), a contradiction. QED
  -/
  intro h
  have he := congrArg (exponent p) h
  rw [exponent_mul p c (m^k) hc (Nat.pow_pos hm),
    exponent_pow p m k hm, exponent_pow p n k hn] at he
  have hd : k ∣ exponent p c + k * exponent p m := ⟨exponent p n, he⟩
  have hs := Nat.dvd_sub (Nat.le_add_left (k * exponent p m) (exponent p c))
    hd (show k ∣ k * exponent p m from ⟨exponent p m, rfl⟩)
  rw [Nat.add_sub_cancel] at hs
  exact hnot hs

theorem no_7_power_2 (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    7 * m ^ 2 ≠ n ^ 2 := by
  /-
  Theorem: There are no positive natural numbers m,n with
  7*m^2=n^2. Proof: The exponent of 7 on the left is
  1+2*e(m); on the right it is 2*e(n). Subtracting would
  make one divisible by 2, which is impossible. QED
  -/
  apply power_equation_obstruction 7 7 2 m n (by decide) hm hn
  rw [exponent_7_7]
  decide

theorem no_24_power_3 (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    24 * m ^ 3 ≠ n ^ 3 := by
  /-
  Theorem: There are no positive natural numbers m,n with
  24*m^3=n^3. Proof: The exponent of 3 on the left is
  1+3*e(m); on the right it is 3*e(n). Subtracting would
  make one divisible by 3, which is impossible. QED
  -/
  apply power_equation_obstruction 3 24 3 m n (by decide) hm hn
  rw [exponent_3_24]
  decide

theorem no_12_power_2 (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    12 * m ^ 2 ≠ n ^ 2 := by
  /-
  Theorem: There are no positive natural numbers m,n with
  12*m^2=n^2. Proof: The exponent of 3 on the left is
  1+2*e(m); on the right it is 2*e(n). Subtracting would
  make one divisible by 2, which is impossible. QED
  -/
  apply power_equation_obstruction 3 12 2 m n (by decide) hm hn
  rw [exponent_3_12]
  decide

theorem no_7_power_3 (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    7 * m ^ 3 ≠ n ^ 3 := by
  /-
  Theorem: There are no positive natural numbers m,n with
  7*m^3=n^3. Proof: The exponent of 7 on the left is
  1+3*e(m); on the right it is 3*e(n). Subtracting would
  make one divisible by 3, which is impossible. QED
  -/
  apply power_equation_obstruction 7 7 3 m n (by decide) hm hn
  rw [exponent_7_7]
  decide

theorem natAbs_power (a : Int) (k : Nat) : (a ^ k).natAbs = a.natAbs ^ k := by
  /-
  Lemma: The absolute value of an integer power is the corresponding
  power of its absolute value. Proof: Induct on the exponent. Both
  zeroth powers are one. The next power multiplies by a; absolute
  values multiply, so the induction equality gives the next case. QED
  -/
  induction k with
  | zero => rfl
  | succ k ih => rw [Int.pow_succ, Int.natAbs_mul, ih, Nat.pow_succ]

theorem no_rational_root (p c k : Nat) (hc : 0 < c) (hk : 0 < k)
    (hnot : ¬ k ∣ exponent p c) (a b : Int) (hb : b ≠ 0) :
    (c : Int) * b ^ k ≠ a ^ k := by
  /-
  Theorem: If some prime exponent in a positive integer c is not a
  multiple of k>0, no integer fraction a/b with b nonzero can be a
  kth root of c.
  Proof: Such a fraction would give c*b^k=a^k after clearing the
  nonzero denominator. Taking absolute values gives
  c*|b|^k=|a|^k. The left side is positive, so |a| is positive too.
  The prime-exponent obstruction now rules out this equation. QED

  Formalization: We state the denominator-cleared integer equation.
  This is precisely the condition for an integer fraction to have kth
  power c. It includes both signs of numerator and denominator and
  avoids importing a construction of real numbers or real roots.
  -/
  intro h
  have he := congrArg Int.natAbs h
  rw [Int.natAbs_mul, Int.natAbs_ofNat, natAbs_power, natAbs_power] at he
  have hbp := Int.natAbs_pos.mpr hb
  have hap : 0 < a.natAbs := by
    have hp := Nat.mul_pos hc (Nat.pow_pos (n := k) hbp)
    by_cases hz : a.natAbs = 0
    · rw [hz, Nat.zero_pow_of_pos k hk] at he
      omega
    · omega
  exact power_equation_obstruction p c k b.natAbs a.natAbs hc hbp hap hnot he

theorem irrational_root_7_2 (a b : Int) (hb : b ≠ 0) :
    (7 : Int) * b ^ 2 ≠ a ^ 2 := by
  /-
  Theorem: The square root of seven is irrational.
  Proof: An integer fraction a/b representing this root, with b
  nonzero, would give 7*b^2=a^2. The exponent of 7 in 7
  is one, which is not divisible by 2. The general rational-root
  obstruction proves that no such numerator and denominator exist.
  The statement uses that equivalent denominator-cleared condition.
  QED
  -/
  apply no_rational_root 7 7 2 (by decide) (by decide) ?_ a b hb
  rw [exponent_7_7]
  decide

theorem irrational_root_12_2 (a b : Int) (hb : b ≠ 0) :
    (12 : Int) * b ^ 2 ≠ a ^ 2 := by
  /-
  Theorem: The square root of twelve is irrational.
  Proof: An integer fraction a/b representing this root, with b
  nonzero, would give 12*b^2=a^2. The exponent of 3 in 12
  is one, which is not divisible by 2. The general rational-root
  obstruction proves that no such numerator and denominator exist.
  The statement uses that equivalent denominator-cleared condition.
  QED
  -/
  apply no_rational_root 3 12 2 (by decide) (by decide) ?_ a b hb
  rw [exponent_3_12]
  decide

theorem irrational_root_7_3 (a b : Int) (hb : b ≠ 0) :
    (7 : Int) * b ^ 3 ≠ a ^ 3 := by
  /-
  Theorem: The cube root of seven is irrational.
  Proof: An integer fraction a/b representing this root, with b
  nonzero, would give 7*b^3=a^3. The exponent of 7 in 7
  is one, which is not divisible by 3. The general rational-root
  obstruction proves that no such numerator and denominator exist.
  The statement uses that equivalent denominator-cleared condition.
  QED
  -/
  apply no_rational_root 7 7 3 (by decide) (by decide) ?_ a b hb
  rw [exponent_7_7]
  decide

theorem prime_not_dvd_iff_coprime (p : Nat) (hp : Prime p) (a : Int) :
    ¬ (p : Int) ∣ a ↔ gcd a p = 1 := by
  /-
  Theorem: An integer is not divisible by a prime exactly when their
  gcd is one. Proof: The nonnegative gcd divides p, so its absolute
  value is either one or p. If p does not divide a, the second case
  is impossible. Conversely, if the gcd is one, a Bezout combination
  equals one. A common divisor p would then divide one, contradicting
  p>1. QED
  -/
  have hg := gcd_data a p
  constructor
  · intro hnot
    have hd := Int.natAbs_dvd_natAbs.mpr hg.2.2.1
    rw [Int.natAbs_ofNat] at hd
    rcases hp.2 (gcd a p).natAbs hd with h | h
    · have he := Int.natAbs_of_nonneg hg.1
      rw [h] at he
      exact he.symm
    · have he := Int.natAbs_of_nonneg hg.1
      rw [h] at he
      exact False.elim (hnot (he ▸ hg.2.1))
  · intro hcop hd
    rcases coprime_bezout a p hcop with ⟨x, y, he⟩
    have hone := dvd_linear p a p x y hd (dvd_refl p)
    rw [he] at hone
    have hle := divisor_le_positive p 1 (by decide) hone
    have hpos := hp.1
    omega

theorem prime_dvd_integer_product (p : Nat) (hp : Prime p) (a b : Int)
    (h : (p : Int) ∣ a * b) : (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  /-
  Theorem: A prime dividing a product of integers divides a factor.
  Proof: If p divides a, we are done. Otherwise a is coprime to p.
  Swapping the gcd arguments and cancelling the coprime factor a
  from p dividing a*b shows that p divides b. QED
  -/
  by_cases ha : (p : Int) ∣ a
  · exact Or.inl ha
  · exact Or.inr (coprime_dvd_cancel p a b h
      (coprime_swap a p ((prime_not_dvd_iff_coprime p hp a).mp ha)))

theorem coprime_divisors (a b u v : Int) (h : gcd a b = 1)
    (hu : u ∣ a) (hv : v ∣ b) : gcd u v = 1 := by
  /-
  Theorem: Divisors of two coprime integers are coprime.
  Proof: Write a=u*s and b=v*t. A Bezout equation a*x+b*y=1
  becomes u*(s*x)+v*(t*y)=1. This combination proves coprimality.
  QED
  -/
  rcases hu with ⟨s, hs⟩
  rcases hv with ⟨t, ht⟩
  rcases coprime_bezout a b h with ⟨x, y, he⟩
  apply coprime_of_bezout u v (s*x) (t*y)
  simpa only [hs, ht, Int.mul_assoc] using he

theorem gcd_eq_of_nonnegative_combination (a b d : Int) (hd : 0 ≤ d)
    (ha : d ∣ a) (hb : d ∣ b) (hxy : ∃ x y : Int, a*x+b*y=d) :
    gcd a b = d := by
  /-
  Lemma: A nonnegative common divisor that is a linear combination
  is the gcd. Proof: For positive d the earlier characterization applies.
  If d is zero, its dividing both inputs makes both inputs zero.
  The gcd's own Bezout combination then forces the gcd to be zero.
  This also covers the convention gcd(0,0)=0. QED
  -/
  by_cases hz : d = 0
  · rcases ha with ⟨s, hs⟩
    rcases hb with ⟨t, ht⟩
    rcases (gcd_data a b).2.2.2 with ⟨x, y, he⟩
    simp only [hz, Int.zero_mul] at hs ht
    rw [hs, ht, Int.zero_mul, Int.zero_mul, Int.add_zero] at he
    rw [hs, ht, hz]
    exact he.symm
  · exact gcd_eq_of_combination a b d (by omega) ha hb hxy

theorem gcd_mul_of_coprime (a b c : Int) (h : gcd b c = 1) :
    gcd a (b*c) = gcd a b * gcd a c := by
  /-
  Theorem: If b and c are coprime, gcd(a,b*c)=gcd(a,b)*gcd(a,c).
  Proof: Put d=gcd(a,b), e=gcd(a,c). Since d divides b and e divides c,
  they are coprime. Both divide a, so d*e divides a. It also divides
  b*c. Choose a*x+b*y=d and a*u+c*v=e. Multiplication gives
  d*e = a*(a*x*u+c*x*v+b*y*u) + (b*c)*(y*v).
  Thus d*e is a nonnegative common divisor expressed as a combination
  of a and b*c. The gcd characterization proves the equality, even
  when some inputs are zero. QED
  -/
  have hd := gcd_data a b
  have he := gcd_data a c
  have hcop := coprime_divisors b c (gcd a b) (gcd a c) h hd.2.2.1 he.2.2.1
  have hda := coprime_product_dvd (gcd a b) (gcd a c) a hd.2.1 he.2.1 hcop
  have hdbc : gcd a b * gcd a c ∣ b*c := by
    rcases hd.2.2.1 with ⟨s, hs⟩
    rcases he.2.2.1 with ⟨t, ht⟩
    exists s*t
    calc
      b*c = (gcd a b*s)*(gcd a c*t) := (congrArg (fun z => z*c) hs).trans (congrArg (fun z => (gcd a b*s)*z) ht)
      _ = (gcd a b*gcd a c)*(s*t) := by
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  apply gcd_eq_of_nonnegative_combination a (b*c) (gcd a b * gcd a c)
    (Int.mul_nonneg hd.1 he.1) hda hdbc
  rcases hd.2.2.2 with ⟨x, y, hx⟩
  rcases he.2.2.2 with ⟨u, v, hu⟩
  exists a*x*u+c*x*v+b*y*u, y*v
  calc
    a*(a*x*u+c*x*v+b*y*u)+(b*c)*(y*v)
        = (a*x+b*y)*(a*u+c*v) := by
            simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            omega
    _ = gcd a b * gcd a c := by rw [hx, hu]

theorem coprime_right_product (a b c : Int) (hb : gcd a b = 1)
    (hc : gcd a c = 1) : gcd a (b*c) = 1 := by
  /-
  Theorem: An integer coprime to each of two integers is coprime to
  their product. Proof: Swap the arguments in both hypotheses, apply
  the product coprimality result, then swap the conclusion back. That
  result multiplies two Bezout equations equal to one, so it needs no
  assumption that b and c are coprime to each other. QED
  -/
  exact coprime_swap (b*c) a
    (coprime_product b c a (coprime_swap a b hb) (coprime_swap a c hc))

theorem distinct_length_bound (xs ys : List Nat) (h : xs.Nodup)
    (hsub : ∀ a ∈ xs, a ∈ ys) : xs.length ≤ ys.length := by
  /-
  Lemma: A list of distinct entries drawn from a list of available
  values cannot be longer than that list.
  Proof: Induct on the list of distinct entries. The empty case is
  immediate. Remove the first entry from both lists. No entry in the
  first tail equals the removed entry, so all its entries remain
  available. Induction bounds the tail length. Restoring the removed
  entry adds one to each length and proves the required bound. QED
  -/
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have hh := List.nodup_cons.mp h
    have ha := hsub a (by simp)
    have ht : ∀ b ∈ xs, b ∈ ys.erase a := by
      intro b hb
      have hne : b ≠ a := by intro he; subst b; exact hh.1 hb
      exact (List.mem_erase_of_ne hne).mpr (hsub b (by simp [hb]))
    have hb := ih (ys.erase a) hh.2 ht
    have hl := List.length_erase_of_mem ha
    have hn : 0 < ys.length := by
      cases ys with
      | nil => cases ha
      | cons b bs => simp
    simp only [List.length_cons]
    omega

theorem repeated_bounded_label (xs : List Nat) (n : Nat)
    (hbound : ∀ a ∈ xs, a < n) (hlen : n < xs.length) :
    ∃ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length),
      i < j ∧ xs[i] = xs[j] := by
  /-
  Lemma: More than n labels drawn from 0,...,n-1 repeat at two
  different positions. Proof: Otherwise every earlier entry differs
  from every later one, making the list distinct. The counting bound
  against the list 0,...,n-1 would give length at most n, contradicting
  the hypothesis. The two positions, not merely two values, are kept
  in the conclusion so that repeated original inputs are covered. QED
  -/
  apply Classical.byContradiction
  intro hnot
  have hdistinct : xs.Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij he
    exact hnot ⟨i, j, hi, hj, hij, he⟩
  have hle := distinct_length_bound xs (List.range n) hdistinct
    (fun a ha => List.mem_range.mpr (hbound a ha))
  rw [List.length_range] at hle
  omega

theorem odd_part_exists (a : Nat) (ha : 0 < a) :
    ∃ r : Nat, 0 < r ∧ r % 2 = 1 ∧ r ≤ a ∧ ∃ k : Nat, a = 2^k*r := by
  /-
  Lemma: Every positive integer is a power of two times a positive
  odd integer no larger than itself.
  Proof: Use strong induction. If a is odd, take r=a and exponent
  zero. Otherwise a=2*q, where 0<q<a. By induction q=2^k*r with
  r odd. Then a=2^(k+1)*r. The bound r≤q<a gives r≤a. This is
  exactly the process of removing factors of two until none remain.
  QED
  -/
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases ho : a % 2 = 1
    · exact ⟨a, ha, ho, Nat.le_refl a, 0, by simp⟩
    · have hqpos : 0 < a/2 := by omega
      have hqsmall : a/2 < a := by omega
      have he : a = 2*(a/2) := by omega
      rcases ih (a/2) hqsmall hqpos with ⟨r, hr, hodd, hle, k, hk⟩
      refine ⟨r, hr, hodd, by omega, k+1, ?_⟩
      calc
        a = 2*(a/2) := he
        _ = 2*(2^k*r) := congrArg (fun t => 2*t) hk
        _ = 2^(k+1)*r := by
          rw [Nat.pow_succ]
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

noncomputable def oddPart (a : Nat) : Nat :=
  if h : 0 < a then Classical.choose (odd_part_exists a h) else 0

theorem oddPart_spec (a : Nat) (ha : 0 < a) :
    0 < oddPart a ∧ oddPart a % 2 = 1 ∧ oddPart a ≤ a ∧
      ∃ k : Nat, a = 2^k * oddPart a := by
  /-
  Lemma: The selected odd part is positive, odd, no larger than the
  input, and leaves a power of two as quotient.
  Proof: Choose an odd part from the preceding decomposition theorem.
  Each assertion is one of the properties supplied by that theorem.
  The value at zero only makes the definition total. QED
  -/
  unfold oddPart
  rw [dif_pos ha]
  exact Classical.choose_spec (odd_part_exists a ha)

theorem same_odd_part_comparable (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (h : oddPart a = oddPart b) : a ∣ b ∨ b ∣ a := by
  /-
  Lemma: Two positive integers with the same odd part are comparable
  by divisibility. Proof: Write a=2^k*r and b=2^l*r. If k≤l, then
  b=a*2^(l-k). If l≤k, then a=b*2^(k-l). These explicit quotients
  establish divisibility in one direction or the other. QED
  -/
  rcases (oddPart_spec a ha).2.2.2 with ⟨k, hk⟩
  rcases (oddPart_spec b hb).2.2.2 with ⟨l, hl⟩
  by_cases hkl : k ≤ l
  · left
    exists 2^(l-k)
    calc
      b = 2^l * oddPart b := hl
      _ = (2^k * 2^(l-k)) * oddPart a := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hkl, h]
      _ = (2^k*oddPart a) * 2^(l-k) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = a * 2^(l-k) := congrArg (fun t => t * 2^(l-k)) hk.symm
  · right
    have hlk : l ≤ k := by omega
    exists 2^(k-l)
    calc
      a = 2^k * oddPart a := hk
      _ = (2^l * 2^(k-l)) * oddPart b := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hlk, h]
      _ = (2^l*oddPart b) * 2^(k-l) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = b * 2^(k-l) := congrArg (fun t => t * 2^(k-l)) hl.symm

theorem dividing_pair (xs : List Nat) (n : Nat)
    (hlen : xs.length = n+1) (hbound : ∀ a ∈ xs, 0 < a ∧ a ≤ 2*n) :
    ∃ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length),
      i ≠ j ∧ xs[i] ∣ xs[j] := by
  /-
  Theorem: Among n+1 positive integers at most 2n, two at distinct
  positions have one dividing the other.
  Proof: Remove factors of two from each input a, leaving an odd
  part r. Because 1≤r≤2n and r is odd, the label r/2 is one of
  0,...,n-1. There are n+1 inputs but only n labels, so two positions
  have equal labels. Odd integers with equal quotients on division
  by two are equal, since both remainders are one. These two inputs
  therefore have the same odd part. Comparing their powers of two
  gives divisibility in one direction. Order the two positions to
  put the divisor first. Repeated input values cause no difficulty:
  the positions are distinct, even if their values coincide. QED
  -/
  let labels := xs.map (fun a => oddPart a / 2)
  have hlabels : ∀ r ∈ labels, r < n := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨a, ha, he⟩
    have hab := hbound a ha
    have hs := oddPart_spec a hab.1
    omega
  have hl : n < labels.length := by simp only [labels, List.length_map]; omega
  rcases repeated_bounded_label labels n hlabels hl with ⟨i,j,hi,hj,hij,he⟩
  have hi' : i < xs.length := by simpa only [labels, List.length_map] using hi
  have hj' : j < xs.length := by simpa only [labels, List.length_map] using hj
  have hai := hbound xs[i] (List.getElem_mem xs i hi')
  have haj := hbound xs[j] (List.getElem_mem xs j hj')
  have hsi := oddPart_spec xs[i] hai.1
  have hsj := oddPart_spec xs[j] haj.1
  have hparts : oddPart xs[i] = oddPart xs[j] := by
    simp only [labels, List.getElem_map] at he
    omega
  rcases same_odd_part_comparable xs[i] xs[j] hai.1 haj.1 hparts with hd | hd
  · exact ⟨i,j,hi',hj',by omega,hd⟩
  · exact ⟨j,i,hj',hi',by omega,hd⟩

end NumberTheory.DivisibilityTests
