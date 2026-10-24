import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ResidueSigns

def magnitude (r : Int) : Nat := if r<0 then (-r).toNat else r.toNat

theorem magnitude_cast (r : Int) :
    (magnitude r : Int)=if r<0 then -r else r := by
  /-
  Lemma: The magnitude label is the absolute value of its integer.
  Proof: If r is negative, -r is nonnegative; otherwise r is.
  Converting either nonnegative integer to a natural and back
  leaves it unchanged. QED
  -/
  by_cases h : r<0
  · simp only [magnitude,if_pos h]
    exact Int.toNat_of_nonneg (by omega)
  · simp only [magnitude,if_neg h]
    exact Int.toNat_of_nonneg (by omega)

theorem power_add (a : Int) (i j : Nat) : a^(i+j)=a^i*a^j := by
  /-
  Lemma: Adding exponents multiplies the corresponding powers.
  Proof: Induct on j. At zero the second factor is one. In the
  successor step, the recursive rule for powers appends one factor
  a. Apply the induction hypothesis and reassociate the product.
  QED
  -/
  induction j with
  | zero => simp [Int.pow_zero]
  | succ j ih =>
    rw [Nat.add_succ,Int.pow_succ,ih,Int.pow_succ,Int.mul_assoc]

def intProduct : List Int → Int
  | [] => 1
  | a::xs => a*intProduct xs

def negativeCount : List Int → Nat
  | [] => 0
  | r::rs => (if r<0 then 1 else 0)+negativeCount rs

theorem signed_product (rs : List Int) :
    intProduct rs=(-1 : Int)^(negativeCount rs)*
      intProduct (rs.map (fun r => (magnitude r : Int))) := by
  /-
  Lemma: A product is the product of its magnitudes times one
  factor of minus one for each negative entry.
  Proof: Induct on the list. A negative first entry contributes
  its negative magnitude and increments the exponent; a
  nonnegative entry contributes its magnitude without a sign.
  Rearranging factors completes either induction step. QED
  -/
  induction rs with
  | nil => simp [intProduct,negativeCount,Int.pow_zero]
  | cons r rs ih =>
    simp only [intProduct,List.map_cons]
    rw [ih,magnitude_cast]
    by_cases h : r<0
    · simp only [negativeCount,if_pos h,power_add]
      simp only [Int.pow_succ,Int.pow_zero,Int.one_mul,Int.neg_mul,Int.mul_neg,
        Int.neg_neg,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.mul_one]
    · simp only [negativeCount,if_neg h,Nat.zero_add]
      simp only [Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]

theorem dvd_refl (a : Int) : a ∣ a := by
  /-
  Theorem: Every integer divides itself.
  Proof: a = a * 1, so choose the integer 1. QED
  -/
  exists 1
  rw [Int.mul_one]

theorem dvd_zero (a : Int) : a ∣ 0 := by
  /-
  Theorem: Every integer divides zero.
  Proof: 0 = a * 0, so choose the integer 0. QED
  -/
  exists 0
  rw [Int.mul_zero]

theorem least_natural (P : Nat → Prop) (h : ∃ b, P b) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b := by
  /-
  Theorem: A nonempty collection of natural numbers has a least member.
  Proof: We prove by strong induction on b that if b is a member, the
  collection has a least member. Strong induction allows us to assume
  the assertion for every natural number smaller than b.

  If some member a is smaller than b, the induction hypothesis at a
  gives a least member. If no member is smaller than b, then b itself
  is least. Finally, nonemptiness supplies a member to start with. QED
  -/
  letI := Classical.propDecidable
  have least_below : ∀ b, P b → ∃ a, P a ∧ ∀ c, P c → a ≤ c := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro hb
      by_cases hs : ∃ a, a < b ∧ P a
      · rcases hs with ⟨a, hab, ha⟩
        exact ih a hab ha
      · exists b
        constructor
        · exact hb
        · intro c hc
          apply Nat.le_of_not_lt
          intro hcb
          exact hs ⟨c, hcb, hc⟩
  rcases h with ⟨b, hb⟩
  exact least_below b hb

theorem division_exists (m n : Nat) (hn : 0 < n) :
    ∃ q r : Int, (m : Int) = (n : Int) * q + r ∧ 0 ≤ r ∧ r < (n : Int) := by
  /-
  Theorem: For a natural number m and a positive natural number n,
  there are integers q and r with m = n * q + r and 0 ≤ r < n.
  Lean includes zero among the natural numbers, so we explicitly require
  n > 0. The conclusion also holds when m = 0.

  Proof: Consider all nonnegative integers r for which m = n * q + r
  for some integer q. This collection is nonempty: q = 0 and r = m
  satisfy the equation. Choose its least member r by well-ordering,
  and choose an integer q giving the equation.

  If r ≥ n, then r - n is nonnegative and

    m = n * q + r = n * (q + 1) + (r - n).

  Thus r - n is another member of the collection. Since n > 0,
  it is smaller than r, contradicting the choice of r. Hence r < n.
  The chosen q and r have all the required properties. QED
  -/
  let P : Nat → Prop := fun r => ∃ q : Int, (m : Int) = (n : Int) * q + r
  have hnonempty : ∃ r, P r := by
    exists m
    exists (0 : Int)
    rw [Int.mul_zero, Int.zero_add]
  rcases least_natural P hnonempty with ⟨r, hr, hleast⟩
  rcases hr with ⟨q, hq⟩
  have hsmall : r < n := by
    apply Nat.lt_of_not_ge
    intro hlarge
    have hnext : P (r - n) := by
      exists q + 1
      rw [Int.mul_add, Int.mul_one]
      -- Since n ≤ r, natural subtraction agrees with integer subtraction.
      omega
    have hminimal := hleast (r - n) hnext
    -- Subtracting positive n gives a strictly smaller natural number.
    omega
  exists q, (r : Int)
  exact ⟨hq, by omega, by omega⟩

theorem dvd_linear (d a b x y : Int) (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ a * x + b * y := by
  /-
  Theorem: A common divisor divides every integer linear combination.
  Proof: Write a = d * u and b = d * v. Then

    a * x + b * y = d * (u * x + v * y).

  The integer u * x + v * y is the required witness. QED
  -/
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  exists u * x + v * y
  rw [hu, hv, Int.mul_add, Int.mul_assoc, Int.mul_assoc]

theorem common_divisor_remainder (a b n r k : Int)
    (h : a = n * b + r) (ha : k ∣ a) (hb : k ∣ b) : k ∣ r := by
  /-
  Theorem: If a = n * b + r, a common divisor of a and b divides r.
  Proof: Subtract n * b from a. A common divisor divides this integer
  linear combination, and a - n * b = r. QED
  -/
  have hd := dvd_linear k a b 1 (-n) ha hb
  rw [Int.mul_one, Int.mul_neg, Int.mul_comm b n] at hd
  have heq : a + -(n * b) = r := by omega
  rw [heq] at hd
  exact hd

theorem common_divisors_step (a b n r k : Int) (h : a = n * b + r) :
    (k ∣ a ∧ k ∣ b) ↔ (k ∣ b ∧ k ∣ r) := by
  /-
  Theorem: Replacing (a, b) by (b, r), where a = n * b + r,
  leaves the common divisors unchanged.
  Proof: The forward implication follows from the preceding theorem.
  Conversely, if k divides b and r, it divides n * b + r = a. QED
  -/
  constructor
  · intro hk
    exact ⟨hk.2, common_divisor_remainder a b n r k h hk.1 hk.2⟩
  · intro hk
    have hd := dvd_linear k b r n 1 hk.1 hk.2
    rw [Int.mul_one, Int.mul_comm b n, ← h] at hd
    exact ⟨hd, hk.1⟩

theorem euclid_natural (a b : Nat) :
    ∃ d : Nat, (d : Int) ∣ (a : Int) ∧ (d : Int) ∣ (b : Int) ∧
      ∃ x y : Int, (a : Int) * x + (b : Int) * y = (d : Int) := by
  /-
  Theorem: The Euclidean procedure produces a nonnegative common divisor
  that is an integer linear combination of the two natural numbers.
  Proof: Use strong induction on the second number b.

  If b = 0, take d = a and coefficients 1 and 0.
  If b > 0, write a = b * q + r with 0 ≤ r < b. Apply the induction
  hypothesis to b and r. It supplies a common divisor d and integers
  x and y with b * x + r * y = d. The preceding common-divisor theorem
  shows that d also divides a. Back-substitution gives

    d = b * x + (a - b * q) * y = a * y + b * (x - q * y).

  These are the required new coefficients. The smaller nonnegative
  remainder ensures that the procedure terminates. QED
  -/
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb : b = 0
    · subst b
      exists a
      refine ⟨dvd_refl a, dvd_zero a, ?_⟩
      exists 1, 0
      rw [Int.mul_one, Int.mul_zero, Int.add_zero]
    · have hbpos : 0 < b := by omega
      rcases division_exists a b hbpos with ⟨q, r, heq, hr, hrb⟩
      have hrnat : (r.toNat : Int) = r := Int.toNat_of_nonneg hr
      rcases ih r.toNat (by omega) b with ⟨d, hdb, hdr, x, y, hxy⟩
      rw [hrnat] at hdr hxy
      have hda := ((common_divisors_step a b q r d
        (by rw [Int.mul_comm]; exact heq)).mpr ⟨hdb, hdr⟩).1
      exists d
      refine ⟨hda, hdb, ?_⟩
      exists y, x - q * y
      have htimes := congrArg (fun t : Int => t * y) heq
      change (a : Int) * y = ((b : Int) * q + r) * y at htimes
      rw [Int.add_mul, Int.mul_assoc] at htimes
      rw [Int.mul_sub]
      omega

theorem euclid_integer (a b : Int) :
    ∃ d : Nat, (d : Int) ∣ a ∧ (d : Int) ∣ b ∧
      ∃ x y : Int, a * x + b * y = (d : Int) := by
  /-
  Theorem: The Euclidean construction also works for arbitrary integers.
  Proof: Apply the natural-number procedure to the absolute values.
  Changing a sign does not change divisibility. If the resulting
  coefficients are x and y, multiply them by the signs of a and b.
  Since a * sign(a) = |a|, the same linear combination gives d. QED
  -/
  rcases euclid_natural a.natAbs b.natAbs with ⟨d, ha, hb, x, y, hxy⟩
  exists d
  constructor
  · rcases ha with ⟨u, hu⟩
    exists a.sign * u
    calc
      a = a.sign * (a.natAbs : Int) := (Int.sign_mul_natAbs a).symm
      _ = (d : Int) * (a.sign * u) := by rw [hu, Int.mul_left_comm]
  · constructor
    · rcases hb with ⟨v, hv⟩
      exists b.sign * v
      calc
        b = b.sign * (b.natAbs : Int) := (Int.sign_mul_natAbs b).symm
        _ = (d : Int) * (b.sign * v) := by rw [hv, Int.mul_left_comm]
    · exists a.sign * x, b.sign * y
      rw [← Int.mul_assoc, Int.mul_sign, ← Int.mul_assoc, Int.mul_sign]
      exact hxy


/-
The Euclidean construction supplies a nonnegative common divisor together
with coefficients. We name that number gcd(a,b). The next proofs verify
that it is the greatest common divisor in the ordinary numerical sense.
We also set gcd(0,0) = 0 through this construction; statements that require
a positive greatest divisor explicitly exclude the pair (0,0).
-/

theorem divisor_le_positive (e d : Int) (hd : 0 < d) (he : e ∣ d) : e ≤ d := by
  /-
  Theorem: A divisor of a positive integer is at most that integer.
  Proof: A nonpositive divisor is already smaller. Otherwise write
  d = e * k with e > 0. If k ≤ 0 then d ≤ 0, a contradiction.
  Thus the integer k is at least 1, and d = e * k ≥ e * 1 = e. QED
  -/
  by_cases hep : 0 < e
  · rcases he with ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_cases hkn : k ≤ 0
      · have hm := Int.mul_le_mul_of_nonneg_left hkn (Int.le_of_lt hep)
        rw [Int.mul_zero, ← hk] at hm
        omega
      · omega
    have hm := Int.mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (Int.le_of_lt hep)
    rw [Int.mul_one, ← hk] at hm
    exact hm
  · omega

def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d=1 ∨ d=p

theorem odd_prime_data (p : Nat) (hp : Prime p) (hodd : p % 2=1) :
    0 < (p-1)/2 ∧ p-1=2*((p-1)/2) ∧ ¬ (p : Int) ∣ 2 := by
  /-
  Lemma: For an odd prime, p-1 is twice a positive integer, and
  p does not divide two. Proof: Oddness and p>1 give p>=3.
  Division by two yields p-1=2*((p-1)/2). A positive divisor of
  two is at most two, so p cannot divide two. QED
  -/
  have hp1 := hp.1
  refine ⟨by omega,by omega,?_⟩
  intro h
  have := divisor_le_positive (p : Int) 2 (by omega) h
  omega

def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a-b

local notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

theorem modeq_symm (a b n : Int) (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  /-
  Theorem: Reversing a congruence preserves it.
  Proof: By the definition of congruence, n is positive and
  a - b = n * k for some integer k. Then

    b - a = -(a - b) = -(n * k) = n * (-k).

  Use -k as the witness. QED
  -/
  rcases h with ⟨hn, k, hk⟩
  constructor
  · exact hn
  · exists -k
    rw [← Int.neg_sub a b, hk, Int.mul_neg]

noncomputable def gcd (a b : Int) : Int := (Classical.choose (euclid_integer a b) : Nat)

theorem gcd_data (a b : Int) :
    0 ≤ gcd a b ∧ gcd a b ∣ a ∧ gcd a b ∣ b ∧
      ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The constructed gcd is nonnegative, divides both inputs,
  and is an integer linear combination of them.
  Proof: These are exactly the properties supplied by the Euclidean
  construction used in its definition. QED
  -/
  constructor
  · unfold gcd
    omega
  · exact Classical.choose_spec (euclid_integer a b)

theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The gcd of two integers is an integer linear combination.
  Proof: These are the coefficients constructed by the Euclidean
  procedure and back-substitution above. The construction also covers
  the harmless extra case a = b = 0. QED
  -/
  exact (gcd_data a b).2.2.2

theorem cancel_coprime (a b c n : Int) (hcop : gcd c n=1)
    (h : Congruent (a*c) (b*c) n) : Congruent a b n := by
  /-
  Theorem: A factor relatively prime to the modulus can be cancelled
  from a congruence.
  Proof: Write (a-b)*c=n*q and c*u+n*v=1. Multiplying the latter
  identity by a-b and substituting the former gives
  a-b=n*(q*u+(a-b)*v). This witness proves the desired congruence.
  QED
  -/
  rcases bezout c n with ⟨u,v,he⟩
  rw [hcop] at he
  rcases h.2 with ⟨q,hq⟩
  have hd : (a-b)*c=n*q := by rw [Int.sub_mul]; exact hq
  refine ⟨h.1,q*u+(a-b)*v,?_⟩
  calc
    a-b = (a-b)*1 := by rw [Int.mul_one]
    _ = (a-b)*(c*u+n*v) := congrArg (fun z => (a-b)*z) he.symm
    _ = ((a-b)*c)*u+n*((a-b)*v) := by
      rw [Int.mul_add,←Int.mul_assoc,Int.mul_left_comm (a-b) n v]
    _ = n*(q*u+(a-b)*v) := by rw [hd,Int.mul_add,Int.mul_assoc]

theorem division_unique (m n q r q' r' : Int) (hn : 0 < n)
    (h : m = n * q + r) (h' : m = n * q' + r')
    (hr : 0 ≤ r) (hrn : r < n) (hr' : 0 ≤ r') (hrn' : r' < n) :
    q = q' ∧ r = r' := by
  /-
  Theorem: Two decompositions with the same positive divisor and
  remainders between zero and n - 1 have equal quotients and remainders.
  We allow any integer m, which also covers natural-number dividends.

  Proof: Suppose m = n * q + r = n * q' + r'. If q < q', the
  quotients are integers, so q + 1 ≤ q'. Multiplying by positive n,

    n * q + n ≤ n * q'.

  But r < n and r' ≥ 0 give

    m = n * q + r < n * q + n ≤ n * q' ≤ n * q' + r' = m.

  This is impossible. Interchanging the two decompositions rules out
  q' < q in exactly the same way. Therefore q = q'. Substituting into
  the original equations and cancelling n * q gives r = r'. QED
  -/
  have hnot : ¬ q < q' := by
    intro hlt
    have hstep : q + 1 ≤ q' := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left hstep (Int.le_of_lt hn)
    rw [Int.mul_add, Int.mul_one] at hmul
    -- The remainder bounds would force m < m.
    omega
  have hnot' : ¬ q' < q := by
    intro hlt
    have hstep : q' + 1 ≤ q := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left hstep (Int.le_of_lt hn)
    rw [Int.mul_add, Int.mul_one] at hmul
    omega
  have hq : q = q' := by omega
  constructor
  · exact hq
  · rw [hq] at h
    omega

theorem bounded_congruent_equal (r s m : Int) (hr : 0 ≤ r) (hrm : r < m)
    (hs : 0 ≤ s) (hsm : s < m) (h : r ≡ s [MOD m]) : r=s := by
  /-
  Lemma: Two congruent integers between zero and m-1 are equal.
  Proof: Write r-s=m*q. Then r=m*q+s and also r=m*0+r.
  Both remainders satisfy the required bounds, so uniqueness of
  quotient and remainder makes r=s. QED
  -/
  rcases h.2 with ⟨q,hq⟩
  exact (division_unique r m 0 r q s h.1 (by simp) (by omega)
    hr hrm hs hsm).2

theorem half_representative_nonzero (p i : Nat) (a r : Int)
    (hp : Prime p) (ho : p%2=1) (ha : gcd a p=1) (hi : i<(p-1)/2)
    (hr : Congruent r (((i : Int)+1)*a) p) : r≠0 := by
  /-
  Lemma: A representative of one of a,2a,...,ha is nonzero,
  where h=(p-1)/2 and a is coprime to p.
  Proof: A zero representative would allow cancellation of a,
  making i+1 congruent to zero. Both lie between zero and p-1,
  so uniqueness of bounded representatives gives i+1=0. QED
  -/
  intro hz
  subst r
  have hh := odd_prime_data p hp ho
  have hc : Congruent (((i : Int)+1)*a) (0*a) p := by
    simpa only [Int.zero_mul] using modeq_symm _ _ p hr
  have he := cancel_coprime ((i : Int)+1) 0 a p ha hc
  have heq := bounded_congruent_equal ((i : Int)+1) 0 p
    (by omega) (by omega) (by omega) (by have := hp.1; omega) he
  omega

theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b + c := by
  /-
  Theorem: A common divisor divides the sum.
  Proof: Write b = a * m and c = a * n. Then

    b + c = a * m + a * n    [Substitution]
          = a * (m + n)      [Distributivity]

  The integer m + n is the required witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m + n
  rw [hm, hn, Int.mul_add]

theorem modeq_trans (a b c n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  /-
  Theorem: Two consecutive congruences combine.
  Proof: The hypotheses tell us that n divides a - b and b - c.
  Therefore n divides their sum. Adding the differences gives:

    (a - b) + (b - c) = a - c.

  Both differences are divisible by n, so their sum is too. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (b - c) h₀.2 h₁.2
    rw [← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem modeq_add (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  /-
  Theorem: Congruences can be added.
  Proof: We must show that n divides (a + c) - (b + d).
  Rearranging the additions and subtractions gives

    (a + c) - (b + d) = (a - b) + (c - d).

  By hypothesis, n divides each term on the right. Our theorem on
  divisibility of sums shows that n divides the left side as well. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (c - d) h₀.2 h₁.2
    have heq : (a + c) - (b + d) = (a - b) + (c - d) := by
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc]
      rw [Int.add_left_comm c (-b)]
    rw [heq]
    exact h

theorem half_magnitudes_distinct (p i j : Nat) (a r s : Int)
    (hp : Prime p) (ho : p%2=1) (ha : gcd a p=1)
    (hi : i<(p-1)/2) (hj : j<(p-1)/2)
    (hr : Congruent r (((i : Int)+1)*a) p)
    (hs : Congruent s (((j : Int)+1)*a) p)
    (he : magnitude r=magnitude s) : i=j := by
  /-
  Lemma: Distinct positions in the half-list have distinct
  magnitudes of their centered representatives.
  Proof: Equal magnitudes imply r=s or r=-s. In the first case,
  cancel a to get i+1 congruent to j+1, hence equality. In the
  second case, cancellation makes i+j+2 congruent to zero.
  This positive sum is at most p-1, an impossibility. QED
  -/
  have hh := odd_prime_data p hp ho
  have hm := congrArg (fun n : Nat => (n : Int)) he
  change (magnitude r : Int)=(magnitude s : Int) at hm
  rw [magnitude_cast,magnitude_cast] at hm
  have hcases : r=s ∨ r= -s := by
    by_cases h1 : r<0 <;> by_cases h2 : s<0 <;> simp [h1,h2] at hm <;> omega
  rcases hcases with hsame | hopp
  · have hc := modeq_trans _ _ _ p (modeq_symm _ _ p hr) (hsame ▸ hs)
    have hd := cancel_coprime ((i : Int)+1) ((j : Int)+1) a p ha hc
    have ht := bounded_congruent_equal ((i : Int)+1) ((j : Int)+1) p
      (by omega) (by omega) (by omega) (by omega) hd
    omega
  · have hc := modeq_add _ _ _ _ p hr hs
    have hz : r+s=0 := by omega
    rw [hz,←Int.add_mul] at hc
    have hd : Congruent ((((i : Int)+1)+((j : Int)+1))*a) (0*a) p := by
      simpa only [Int.zero_mul] using modeq_symm _ _ p hc
    have ht := cancel_coprime (((i : Int)+1)+((j : Int)+1)) 0 a p ha hd
    have heq := bounded_congruent_equal (((i : Int)+1)+((j : Int)+1)) 0 p
      (by omega) (by omega) (by omega) (by have := hp.1; omega) ht
    omega

theorem centered_magnitude_range (p i : Nat) (a r : Int)
    (hp : Prime p) (ho : p%2=1) (ha : gcd a p=1) (hi : i<(p-1)/2)
    (hr : Congruent r (((i : Int)+1)*a) p)
    (hb : -((p-1)/2 : Nat) ≤ r ∧ r ≤ ((p-1)/2 : Nat)) :
    0 < magnitude r ∧ magnitude r ≤ (p-1)/2 := by
  /-
  Lemma: The magnitudes of the centered representatives lie in
  1,...,h. Proof: Centering bounds the absolute value by h, and
  the preceding nonzero lemma excludes magnitude zero. QED
  -/
  have hn := half_representative_nonzero p i a r hp ho ha hi hr
  have hm := magnitude_cast r
  by_cases h : r<0 <;> simp only [h,if_true,if_false] at hm <;> omega

theorem distinct_subset_perm (xs ys : List Nat) (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) (hlen : xs.length=ys.length) : xs.Perm ys := by
  /-
  Lemma: Distinct entries drawn from a list of the same length
  rearrange that list. Proof: Induct on the first list. Remove its
  head from both lists. Distinctness ensures its tail still lies
  in the second list after removal, and lengths remain equal.
  Apply induction, then restore the head. The empty case follows
  because the second list also has length zero. QED
  -/
  letI : BEq Nat := instBEqOfDecidableEq
  induction xs generalizing ys with
  | nil =>
    have hy : ys=[] := List.length_eq_zero.mp (by simpa using hlen.symm)
    subst ys; exact List.Perm.refl []
  | cons a xs ih =>
    have hh := List.nodup_cons.mp hnd
    have ha := hsub a (by simp)
    have ht : ∀ b ∈ xs, b ∈ ys.erase a := by
      intro b hb
      have hne : b ≠ a := by intro he; subst b; exact hh.1 hb
      exact (List.mem_erase_of_ne hne).mpr (hsub b (by simp [hb]))
    have he := List.length_erase_of_mem ha
    have hp := ih (ys.erase a) hh.2 ht (by simp only [List.length_cons] at hlen; omega)
    exact (hp.cons a).trans (List.perm_cons_erase ha).symm

theorem centered_magnitudes_perm (p : Nat) (a : Int) (r : Nat → Int)
    (hp : Prime p) (ho : p%2=1) (ha : gcd a p=1)
    (hr : ∀ i<(p-1)/2, Congruent (r i) (((i : Int)+1)*a) p)
    (hb : ∀ i<(p-1)/2, -((p-1)/2 : Nat) ≤ r i ∧ r i ≤ ((p-1)/2 : Nat)) :
    ((List.range ((p-1)/2)).map (fun i : Nat => magnitude (r i))).Perm
      ((List.range ((p-1)/2)).map (fun i : Nat => i+1)) := by
  /-
  Lemma: The centered magnitudes rearrange 1,...,h.
  Proof: They lie in that interval and have no repetitions by
  the preceding lemmas. There are h entries on each side.
  A distinct list drawn from another list of the same length
  is a rearrangement of it. QED
  -/
  apply distinct_subset_perm
  · apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ (List.nodup_range ((p-1)/2))
    intro i j hi hj hij he
    exact hij (half_magnitudes_distinct p i j a (r i) (r j) hp ho ha
      (List.mem_range.mp hi) (List.mem_range.mp hj)
      (hr i (List.mem_range.mp hi)) (hr j (List.mem_range.mp hj)) he)
  · intro m hm
    rcases List.mem_map.mp hm with ⟨i,hi,he⟩
    have hi' := List.mem_range.mp hi
    have hm' := centered_magnitude_range p i a (r i) hp ho ha hi' (hr i hi') (hb i hi')
    apply List.mem_map.mpr
    exact ⟨m-1,List.mem_range.mpr (by omega),by omega⟩
  · simp only [List.length_map]

theorem gcd_positive (a b : Int) (h : a ≠ 0 ∨ b ≠ 0) : 0 < gcd a b := by
  /-
  Theorem: The gcd is positive when the inputs are not both zero.
  Proof: It is nonnegative. If it were zero, divisibility of a and b
  would express both as zero times an integer, forcing a = b = 0.
  This contradicts the hypothesis. QED
  -/
  rcases gcd_data a b with ⟨hn, ⟨u, hu⟩, ⟨v, hv⟩, hxy⟩
  by_cases hz : gcd a b = 0
  · rw [hz, Int.zero_mul] at hu hv
    rcases h with ha | hb
    · exact False.elim (ha hu)
    · exact False.elim (hb hv)
  · omega

theorem prime_coprime (a : Int) (p : Nat) (hp : Prime p) (ha : ¬ (p : Int) ∣ a) :
    gcd a p=1 := by
  /-
  Lemma: An integer not divisible by a prime is relatively prime
  to it. Proof: The positive gcd d divides p, so primality makes
  d either one or p. The latter would imply p divides a, which
  is excluded. Hence d=1. QED
  -/
  have hd := gcd_positive a p (Or.inr (by have := hp.1; omega))
  have hcast := Int.toNat_of_nonneg (Int.le_of_lt hd)
  have hdiv : (gcd a p).toNat ∣ p := by
    apply Int.ofNat_dvd.mp
    rw [hcast]
    exact (gcd_data a p).2.2.1
  rcases hp.2 _ hdiv with h | h
  · omega
  · have he : gcd a p=(p : Int) := by omega
    have had := (gcd_data a p).2.1
    rw [he] at had
    exact False.elim (ha had)

theorem product_perm (xs ys : List Int) (h : xs.Perm ys) : intProduct xs=intProduct ys := by
  /-
  Lemma: Rearranging a finite list preserves its product.
  Proof: The elementary rearrangement steps are keeping a common
  head, swapping adjacent entries, and composing rearrangements.
  Induction on these steps uses multiplication's associativity and
  commutativity for a swap, and equality for the other steps. QED
  -/
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [intProduct,ih]
  | swap a b xs => simp only [intProduct,Int.mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem product_append (xs ys : List Int) : intProduct (xs++ys)=intProduct xs*intProduct ys := by
  /-
  Lemma: The product of two joined lists is the product of their
  products. Proof: Induct on the first list. Its empty product is
  one; in the next case, use induction on the tail and reassociate
  the leading factor. QED
  -/
  induction xs with
  | nil => simp [intProduct]
  | cons a xs ih =>
    change a*intProduct (xs++ys)=(a*intProduct xs)*intProduct ys
    rw [ih,Int.mul_assoc]

def factorial : Nat → Int
  | 0 => 1
  | n+1 => ((n+1 : Nat) : Int)*factorial n

theorem factorial_product (n : Nat) :
    factorial n=intProduct (((List.range n).map (fun i => i+1)).map (fun i : Nat => (i : Int))) := by
  /-
  Lemma: The recursively defined factorial is the product of the
  list 1,...,n. Proof: At zero both products are empty and equal
  one. Increasing n appends n+1 to the list. Split off that final
  factor and use induction; commutativity puts it in the order
  used by the factorial recursion. QED
  -/
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [factorial,List.range_succ,List.map_append,List.map_cons,List.map_nil,
      product_append,intProduct,Int.mul_one]
    rw [ih,Int.mul_comm]

theorem centered_product (p : Nat) (a : Int) (r : Nat → Int)
    (hp : Prime p) (ho : p%2=1) (ha : ¬ (p : Int) ∣ a)
    (hr : ∀ i<(p-1)/2, Congruent (r i) (((i : Int)+1)*a) p)
    (hb : ∀ i<(p-1)/2, -((p-1)/2 : Nat) ≤ r i ∧ r i ≤ ((p-1)/2 : Nat)) :
    intProduct ((List.range ((p-1)/2)).map r)=
      (-1 : Int)^(negativeCount ((List.range ((p-1)/2)).map r))*factorial ((p-1)/2) := by
  /-
  Theorem: The product of the centered representatives is h!
  times a sign for each negative entry.
  Proof: The signed-product identity separates the signs from
  the magnitudes. The magnitudes rearrange 1,...,h, so their
  product is h!. QED
  -/
  rw [signed_product]
  have hperm := (centered_magnitudes_perm p a r hp ho (prime_coprime a p hp ha) hr hb).map
    (fun n : Nat => (n : Int))
  have he := product_perm _ _ hperm
  rw [←factorial_product] at he
  simp only [List.map_map,Function.comp_def] at he ⊢
  rw [he]

theorem modeq_refl (a n : Int) (hn : 0 < n) : a ≡ a [MOD n] := by
  /-
  Theorem: Every integer is congruent to itself.
  Proof: The modulus n is positive by hypothesis. Also,

    a - a = 0 = n * 0.

  Thus n divides a - a, using the integer 0. QED
  -/
  constructor
  · exact hn
  · exists 0
    rw [Int.sub_self, Int.mul_zero]

theorem sign_congruent_equal (u v : Int) (p : Nat) (hp : Prime p) (ho : p%2=1)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (h : Congruent u v p) : u=v := by
  /-
  Lemma: Two signs congruent modulo an odd prime are equal.
  Proof: Add one to both. The resulting representatives are
  zero or two, both less than the odd prime. Uniqueness of
  bounded representatives makes them equal. Subtract one. QED
  -/
  have hh := odd_prime_data p hp ho
  have h' := modeq_add _ _ 1 1 p h (modeq_refl 1 p (by have := hp.1; omega))
  have he := bounded_congruent_equal (u+1) (v+1) p
    (by rcases hu with h|h <;> omega) (by rcases hu with h|h <;> omega)
    (by rcases hv with h|h <;> omega) (by rcases hv with h|h <;> omega) h'
  omega

theorem bezout_product (a b c : Int)
    (hb : ∃ u v : Int, a*u+b*v=1) (hc : ∃ u v : Int, a*u+c*v=1) :
    ∃ u v : Int, a*u+(b*c)*v=1 := by
  /-
  Lemma: If a has a linear combination equal to one with each of
  b and c, it also has one with b*c.
  Proof: Write a*u+b*v=1 and a*p+c*q=1. Multiply the second
  equality by b*v and substitute for b*v in the first. We obtain
  a*(u+b*v*p)+(b*c)*(v*q)=1. These are the required coefficients.
  QED
  -/
  rcases hb with ⟨u,v,hu⟩
  rcases hc with ⟨p,q,hp⟩
  refine ⟨u+b*v*p,v*q,?_⟩
  have he := congrArg (fun t => t*(b*v)) hp
  simp only [Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_assoc,
    Int.mul_left_comm,Int.mul_comm,Int.mul_one] at he ⊢
  omega

theorem gcd_one_right (a n : Int) (hn : 0 < n)
    (h : ∃ u v : Int, a*u+n*v=1) : gcd a n=1 := by
  /-
  Lemma: A positive modulus n and a linear combination a*u+n*v=1
  imply gcd(a,n)=1, even when a is zero or negative.
  Proof: The positive gcd divides this linear combination, so it
  divides one and is at most one. Positivity makes it exactly one.
  QED
  -/
  rcases h with ⟨u,v,he⟩
  have hd := dvd_linear (gcd a n) a n u v
    (gcd_data a n).2.1 (gcd_data a n).2.2.1
  rw [he] at hd
  have hle := divisor_le_positive (gcd a n) 1 (by decide) hd
  have hp := gcd_positive a n (Or.inr (by omega))
  omega

theorem coprime_product (xs : List Int) (n : Int) (hn : 0 < n)
    (hc : ∀ x ∈ xs, gcd x n=1) : gcd (intProduct xs) n=1 := by
  /-
  Lemma: A product of integers coprime to n is coprime to n.
  Proof: Inductively construct a Bezout identity for n and the
  product. The empty product is one. For a nonempty list, combine
  the identity for n and the head with the one for n and the tail
  product. Reverse the order of terms to identify the gcd as one.
  QED
  -/
  have hb : ∃ u v : Int, n*u+intProduct xs*v=1 := by
    induction xs with
    | nil => exact ⟨0,1,by simp [intProduct]⟩
    | cons x xs ih =>
      rcases bezout x n with ⟨u,v,he⟩
      rw [hc x (by simp)] at he
      exact bezout_product n x (intProduct xs) ⟨v,u,by omega⟩
        (ih (fun y hy => hc y (by simp [hy])))
  rcases hb with ⟨u,v,he⟩
  exact gcd_one_right _ n hn ⟨v,u,by omega⟩

theorem small_prime_coprime (p i : Nat) (hp : Prime p) (hi : 0 < i) (hip : i < p) :
    gcd (i : Int) p=1 := by
  /-
  Lemma: Each positive integer below p is relatively prime to p.
  Proof: If p divided i, the divisor bound for positive i would
  force p≤i. This contradicts i<p, so the preceding lemma applies.
  QED
  -/
  apply prime_coprime i p hp
  intro h
  have hb := divisor_le_positive p i (by omega) h
  omega

theorem half_factorial_coprime (p : Nat) (hp : Prime p) (ho : p%2=1) :
    gcd (factorial ((p-1)/2)) p=1 := by
  /-
  Lemma: The factorial of h=(p-1)/2 is coprime to p.
  Proof: Each factor lies between one and h, hence strictly
  below p, and is coprime to p. Their product is coprime too. QED
  -/
  rw [factorial_product]
  apply coprime_product _ p (by have := hp.1; omega)
  intro x hx
  rcases List.mem_map.mp hx with ⟨i,hi,rfl⟩
  rcases List.mem_map.mp hi with ⟨j,hj,rfl⟩
  have hj' := List.mem_range.mp hj
  have hh := odd_prime_data p hp ho
  exact small_prime_coprime p (j+1) hp (by omega) (by omega)

theorem dvd_mult_of_dvd_left (a b c : Int) (h : a ∣ b) : a ∣ b * c := by
  /-
  Theorem: If a divides b, then a divides b * c for any integer c.
  Proof: If b = a * m, then

    b * c = (a * m) * c = a * (m * c).

  Use m * c as the witness. QED
  -/
  rcases h with ⟨m, hm⟩
  exists m * c
  rw [hm, Int.mul_assoc]

theorem modeq_mult (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] := by
  /-
  Theorem: Congruences can be multiplied.
  Proof: We must show that n divides a * c - b * d. We can express
  this difference in terms of a - b and c - d:

    a * c - b * d = a * c - b * c + b * c - b * d
                 = (a - b) * c + b * (c - d).

  Since n divides a - b, it divides (a - b) * c. Similarly, since n
  divides c - d, it divides b * (c - d). It therefore divides their
  sum, which is a * c - b * d. QED
  -/
  constructor
  · exact h₀.1
  · have h₂ := dvd_mult_of_dvd_left n (a - b) c h₀.2
    have h₃ := dvd_mult_of_dvd_left n (c - d) b h₁.2
    have h := dvd_add n ((a - b) * c) ((c - d) * b) h₂ h₃
    rw [Int.mul_comm (c - d) b, Int.sub_mul, Int.mul_sub,
      ← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem product_congruent (xs : List Nat) (f g : Nat → Int) (n : Int) (hn : 0 < n)
    (h : ∀ i ∈ xs, Congruent (f i) (g i) n) :
    Congruent (intProduct (xs.map f)) (intProduct (xs.map g)) n := by
  /-
  Lemma: Products of corresponding congruent factors are congruent.
  Proof: Induct on the list. Empty products are both one. For a
  nonempty list multiply the head congruence by the congruence
  of the remaining products supplied by induction. QED
  -/
  induction xs with
  | nil => exact modeq_refl 1 n hn
  | cons i xs ih =>
    exact modeq_mult _ _ _ _ n (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem scaled_product (xs : List Nat) (a : Int) :
    intProduct (xs.map (fun i : Nat => (i : Int)*a))=
      a^xs.length*intProduct (xs.map (fun i : Nat => (i : Int))) := by
  /-
  Lemma: Multiplying every entry by a inserts a factor a raised
  to the number of entries into the total product.
  Proof: Induct on the list. Empty products and a^0 are one.
  Restoring one head inserts one more factor a. Reassociate and
  commute the factors to obtain the successor power. QED
  -/
  induction xs with
  | nil => simp [intProduct,Int.pow_zero]
  | cons i xs ih =>
    simp only [List.map_cons,List.length_cons,intProduct]
    rw [ih,Int.pow_succ]
    simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]

theorem congruent_coprime (a b n : Int) (hcop : gcd a n=1)
    (h : Congruent a b n) : gcd b n=1 := by
  /-
  Theorem: Replacing a number by a congruent integer preserves
  coprimality with the modulus.
  Proof: Write a-b=n*q and a*u+n*v=1. Substitution gives
  b*u+n*(q*u+v)=1. This is a Bezout identity for b and n,
  so their gcd is one. QED
  -/
  rcases bezout a n with ⟨u,v,he⟩
  rw [hcop] at he
  rcases h.2 with ⟨q,hq⟩
  apply gcd_one_right b n h.1
  refine ⟨u,q*u+v,?_⟩
  have ht := congrArg (fun z => z*u) hq
  change (a-b)*u=(n*q)*u at ht
  rw [Int.sub_mul,Int.mul_assoc] at ht
  rw [Int.mul_add]
  omega

theorem gcd_one_combination (a n : Int) (h : ∃ u v : Int, a*u+n*v=1) : gcd a n=1 := by
  /-
  Lemma: A linear combination equal to one forces the gcd to be
  one, without any sign restriction on either input. Proof: The
  nonnegative gcd divides the combination one. It cannot be zero,
  and a divisor of one is at most one, so it equals one. QED
  -/
  rcases h with ⟨u,v,he⟩
  have hd := dvd_linear (gcd a n) a n u v (gcd_data a n).2.1 (gcd_data a n).2.2.1
  rw [he] at hd
  have hb := divisor_le_positive (gcd a n) 1 (by decide) hd
  have hp := (gcd_data a n).1
  have hz : gcd a n ≠ 0 := by
    intro hzero
    rcases hd with ⟨k,hk⟩
    rw [hzero,Int.zero_mul] at hk
    omega
  omega

theorem coprime_product_iff (a m n : Int) :
    gcd a (m*n)=1 ↔ gcd a m=1 ∧ gcd a n=1 := by
  /-
  Lemma: An integer is coprime to a product exactly when it is
  coprime to each factor.
  Proof: A Bezout identity a*u+(m*n)*v=1 is also an identity for
  a,m and for a,n, by regrouping the second term. Conversely,
  combining identities for a,m and a,n gives one for a,m*n.
  The Bezout characterization proves both directions. QED
  -/
  constructor
  · intro hc
    rcases bezout a (m*n) with ⟨u,v,he⟩
    rw [hc] at he
    constructor
    · apply gcd_one_combination a m
      exact ⟨u,n*v,by simpa only [Int.mul_assoc] using he⟩
    · apply gcd_one_combination a n
      exact ⟨u,m*v,by simpa only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using he⟩
  · rintro ⟨hm,hn⟩
    rcases bezout a m with ⟨u,v,hu⟩
    rcases bezout a n with ⟨s,t,hs⟩
    rw [hm] at hu
    rw [hn] at hs
    exact gcd_one_combination a (m*n) (bezout_product a m n ⟨u,v,hu⟩ ⟨s,t,hs⟩)

theorem coprime_power_iff (a m : Int) (k : Nat) :
    gcd a (m^(k+1))=1 ↔ gcd a m=1 := by
  /-
  Lemma: Coprimality to a positive power is equivalent to
  coprimality to its base.
  Proof: The first power is the base. For the induction step,
  split m^(k+2) into m^(k+1)*m. Coprimality to this product is
  equivalent to coprimality to both factors, which by induction
  is just the single condition for m. QED
  -/
  induction k with
  | zero => simp only [Nat.zero_add,Int.pow_succ,Int.pow_zero,Int.one_mul]
  | succ k ih =>
    rw [Int.pow_succ,coprime_product_iff,ih]
    exact ⟨fun h => h.1,fun h => ⟨h,h⟩⟩

theorem root_is_coprime (x b : Int) (n k : Nat) (hk : 0 < k)
    (hb : gcd b n=1) (h : Congruent (x^k) b n) : gcd x n=1 := by
  /-
  Lemma: A positive-power root of a coprime residue is coprime
  to the modulus. Proof: Congruence makes x^k coprime whenever
  b is coprime. Coprimality to a positive power is equivalent to
  coprimality to the base, using the product criterion. QED
  -/
  have hc := congruent_coprime b (x^k) n hb (modeq_symm _ _ n h)
  -- Reverse the inputs using their Bezout identity.
  have hswap : gcd (n : Int) (x^k)=1 := by
    rcases bezout (x^k) n with ⟨s,t,he⟩
    rw [hc] at he
    exact gcd_one_combination n (x^k) ⟨t,s,by omega⟩
  have he : k=(k-1)+1 := by omega
  rw [he] at hswap
  have hc' := (coprime_power_iff n x (k-1)).mp hswap
  rcases bezout (n : Int) x with ⟨s,t,hs⟩
  rw [hc'] at hs
  exact gcd_one_combination x n ⟨t,s,by omega⟩

theorem integer_division_exists (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ q r : Int, a=(n : Int)*q+r ∧ 0 ≤ r ∧ r < n := by
  /-
  Lemma: Every integer has a quotient and a nonnegative remainder
  less than a positive natural divisor n.
  Proof: Let t=|a|. Since n≥1, a+n*t≥a+|a|≥0. Divide this
  nonnegative integer by n using the well-ordering construction.
  If a+n*t=n*q+r, then a=n*(q-t)+r, with the same remainder bounds.
  QED
  -/
  let t : Int := a.natAbs
  have ht : 0 ≤ t := by dsimp [t]; omega
  have ha : -a ≤ t := by
    have h : -a ≤ (-a).natAbs := Int.le_natAbs
    simpa only [Int.natAbs_neg] using h
  have hmul := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ n) ht
  rw [Int.one_mul] at hmul
  have hnonneg : 0 ≤ a+(n : Int)*t := by omega
  rcases division_exists (a+(n : Int)*t).toNat n hn with ⟨q,r,he,hr,hrn⟩
  rw [Int.toNat_of_nonneg hnonneg] at he
  refine ⟨q-t,r,?_,hr,hrn⟩
  rw [Int.mul_sub]
  omega

theorem canonical_residue (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ r : Int, 0 ≤ r ∧ r < n ∧ a ≡ r [MOD (n : Int)] ∧
      ∀ s : Int, 0 ≤ s → s < n → a ≡ s [MOD (n : Int)] → s=r := by
  /-
  Theorem: Every integer is congruent to exactly one integer among
  zero through n-1, for positive n.
  Proof: Division gives a=n*q+r with 0≤r<n, so a-r=n*q proves
  congruence. If s is another such representative, reverse the
  congruence a≡s and combine it with a≡r to get s≡r. Bounded
  congruent representatives are equal. QED
  -/
  rcases integer_division_exists a n hn with ⟨q,r,he,hr,hrn⟩
  have hcong : a ≡ r [MOD (n : Int)] := ⟨by omega,q,by omega⟩
  refine ⟨r,hr,hrn,hcong,?_⟩
  intro s hs hsn hsc
  exact bounded_congruent_equal s r n hs hsn hr hrn
    (modeq_trans s a r n (modeq_symm a s n hsc) hcong)

noncomputable def canonicalLabel (a : Int) (n : Nat) : Nat :=
  if h : 0 < n then (Classical.choose (canonical_residue a n h)).toNat else 0

theorem canonicalLabel_spec (a : Int) (n : Nat) (hn : 0 < n) :
    canonicalLabel a n < n ∧ a ≡ (canonicalLabel a n : Int) [MOD (n : Int)] := by
  /-
  Lemma: The canonical label is less than n and represents its input.
  Proof: Choose the unique representative already proved to exist.
  It is nonnegative, so conversion to a natural number preserves its
  value and both stated properties. At modulus zero the definition
  is total by convention, but the lemma requires positive modulus.
  QED
  -/
  have h := Classical.choose_spec (canonical_residue a n hn)
  have hcast := Int.toNat_of_nonneg h.1
  unfold canonicalLabel
  rw [dif_pos hn]
  constructor
  · omega
  · rw [Int.toNat_of_nonneg h.1]
    exact h.2.2.1

theorem canonicalLabel_eq_iff (a b : Int) (n : Nat) (hn : 0 < n) :
    canonicalLabel a n = canonicalLabel b n ↔ a ≡ b [MOD (n : Int)] := by
  /-
  Lemma: Two inputs have the same canonical label exactly when they
  are congruent. Proof: Equal labels give a common representative;
  transitivity yields congruence of the inputs. Conversely, congruent
  inputs have congruent labels by symmetry and transitivity. Both
  labels lie between zero and n-1, so they are equal. QED
  -/
  have ha := canonicalLabel_spec a n hn
  have hb := canonicalLabel_spec b n hn
  constructor
  · intro he
    have hac := ha.2
    rw [he] at hac
    exact modeq_trans a (canonicalLabel b n) b n hac (modeq_symm b _ n hb.2)
  · intro h
    have hlabels := modeq_trans (canonicalLabel a n) a (canonicalLabel b n) n
      (modeq_symm a _ n ha.2) (modeq_trans a b _ n h hb.2)
    have he := bounded_congruent_equal (canonicalLabel a n) (canonicalLabel b n) n
      (by omega) (by omega) (by omega) (by omega) hlabels
    omega

theorem scaled_labels_injective (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1)
    (i j : Nat) (hi : i < n) (hj : j < n)
    (he : canonicalLabel ((i : Int)*a) n=canonicalLabel ((j : Int)*a) n) : i=j := by
  /-
  Lemma: Multiplication by a coprime integer gives distinct residue
  labels to distinct canonical representatives. Proof: Equal labels
  give i*a congruent to j*a. Cancel a; the representatives i and j
  lie between zero and n-1, so their congruence makes them equal.
  QED
  -/
  have h := (canonicalLabel_eq_iff _ _ n hn).mp he
  have hcancel := cancel_coprime i j a n hc h
  have hb := bounded_congruent_equal i j n (by omega) (by omega)
    (by omega) (by omega) hcancel
  omega

def nonzeroResidues (n : Nat) : List Nat := (List.range n).erase 0

theorem nonzero_residues_mem (n i : Nat) : i ∈ nonzeroResidues n ↔ 0 < i ∧ i < n := by
  /-
  Lemma: Removing zero from the canonical list leaves exactly the
  positive integers below n. Proof: Membership in the range means
  i<n. Its entries are distinct, so erasing zero removes precisely
  zero. For i≠0 membership is unchanged. QED
  -/
  by_cases hi : i=0
  · subst i
    simp [nonzeroResidues,List.Nodup.not_mem_erase (List.nodup_range n)]
  · rw [nonzeroResidues,List.mem_erase_of_ne hi,List.mem_range]
    omega

theorem coprime_not_zero (a : Int) (n : Nat) (hn : 1 < n) (hc : gcd a n=1) :
    ¬ Congruent a 0 n := by
  /-
  Lemma: A number coprime to a modulus greater than one cannot be
  congruent to zero. Proof: Otherwise n divides a and n. It then
  divides the Bezout combination one, forcing n≤1, a contradiction.
  QED
  -/
  intro h
  have ha : (n : Int) ∣ a := by simpa using h.2
  rcases bezout a n with ⟨u,v,he⟩
  rw [hc] at he
  have hd := dvd_linear n a n u v ha (dvd_refl n)
  rw [he] at hd
  have hb := divisor_le_positive n 1 (by decide) hd
  omega

theorem nonzero_labels_perm (a : Int) (p : Nat) (hp : Prime p) (hc : gcd a p=1) :
    ((nonzeroResidues p).map (fun i : Nat => canonicalLabel ((i : Int)*a) p)).Perm
      (nonzeroResidues p) := by
  /-
  Lemma: Multiplication by a coprime integer rearranges the nonzero
  residue labels modulo a prime. Proof: Cancellation makes the
  labels distinct. Each factor i and a is coprime to p, so their
  product has a Bezout identity with p and cannot have label zero.
  Thus all labels belong to the nonzero list. The lengths agree,
  so the distinct-selection lemma gives the rearrangement. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hnd0 : (nonzeroResidues p).Nodup := (List.nodup_range p).erase 0
  have hnd : ((nonzeroResidues p).map (fun i : Nat => canonicalLabel ((i : Int)*a) p)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ hnd0
    intro i j hi hj hne he
    exact hne (scaled_labels_injective a p hn hc i j
      ((nonzero_residues_mem p i).mp hi).2 ((nonzero_residues_mem p j).mp hj).2 he)
  apply distinct_subset_perm _ _ hnd ?_ (by simp)
  intro r hr
  rcases List.mem_map.mp hr with ⟨i,hi,he⟩
  subst r
  have hib := (nonzero_residues_mem p i).mp hi
  have hs := canonicalLabel_spec ((i : Int)*a) p hn
  apply (nonzero_residues_mem p _).mpr
  refine ⟨?_,hs.1⟩
  have hzero : canonicalLabel ((i : Int)*a) p ≠ 0 := by
    intro hz
    rw [hz] at hs
    have hcancel := cancel_coprime i 0 a p hc (by simpa using hs.2)
    exact coprime_not_zero i p hp.1 (small_prime_coprime p i hp hib.1 hib.2) hcancel
  omega

theorem residue_product_congruent (a : Int) (p : Nat) (hp : Prime p) (hc : gcd a p=1) :
    Congruent (intProduct ((nonzeroResidues p).map (fun i : Nat => (i : Int)*a)))
      (intProduct ((nonzeroResidues p).map (fun i : Nat => (i : Int)))) p := by
  /-
  Theorem: The product a*(2*a)*...*((p-1)*a) is congruent to
  1*2*...*(p-1). Proof: Replace each factor by its canonical label.
  The products are congruent because corresponding factors are.
  The labels rearrange the nonzero canonical residues, so their
  product equals the product of those residues. QED
  -/
  have h := product_congruent (nonzeroResidues p) (fun i : Nat => (i : Int)*a)
    (fun i : Nat => (canonicalLabel ((i : Int)*a) p : Int)) p
    (by have := hp.1; omega) (fun i _ => (canonicalLabel_spec _ p (by have := hp.1; omega)).2)
  have he := product_perm _ _ ((nonzero_labels_perm a p hp hc).map (fun i : Nat => (i : Int)))
  simp only [List.map_map,Function.comp_def] at he
  rw [he] at h
  exact h

theorem fermat_coprime (a : Int) (p : Nat) (hp : Prime p) (hc : gcd a p=1) :
    Congruent (a^(p-1)) 1 p := by
  /-
  Theorem: For a prime p and an integer a relatively prime to p,
  a^(p-1) is congruent to one modulo p.
  Proof: Let P be the product of the positive integers below p.
  The residue product theorem gives a^(p-1)*P congruent to P,
  because scaling each of its p-1 factors extracts a^(p-1).
  Each factor of P is coprime to p, hence so is P. Cancelling P
  gives the asserted congruence. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hl : (nonzeroResidues p).length=p-1 := by
    have he := List.length_erase_of_mem (by simp; omega : 0 ∈ List.range p)
    simp only [List.length_range] at he
    exact he
  have h := residue_product_congruent a p hp hc
  rw [scaled_product,hl] at h
  have hprod := coprime_product ((nonzeroResidues p).map (fun i : Nat => (i : Int)))
    p (by omega) (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨i,hi,he⟩
      subst x
      have hib := (nonzero_residues_mem p i).mp hi
      exact small_prime_coprime p i hp hib.1 hib.2)
  exact cancel_coprime (a^(p-1)) 1 _ p hprod (by simpa using h)

theorem power_mul (a : Int) (i j : Nat) : (a^i)^j=a^(i*j) := by
  /-
  Lemma: Raising a power to another power multiplies exponents.
  Proof: Induct on j. At zero both sides are one. The successor
  multiplies the preceding power by a^i, which adds i to its
  exponent and gives i*(j+1). QED
  -/
  induction j with
  | zero => simp [Int.pow_zero]
  | succ j ih => rw [Int.pow_succ,ih,Nat.mul_succ,power_add]

theorem modeq_pow_step (a b n : Int) (k : Nat)
    (h : a ≡ b [MOD n]) (hk : a ^ k ≡ b ^ k [MOD n]) :
    a ^ (k + 1) ≡ b ^ (k + 1) [MOD n] := by
  /-
  Theorem: Advance an exponent by one.
  Proof: a ^ (k + 1) = a ^ k * a, and likewise for b.
  Multiply the two assumed congruences. QED
  -/
  rw [Int.pow_succ, Int.pow_succ]
  exact modeq_mult (a ^ k) (b ^ k) a b n hk h

theorem modeq_pow (a b n : Int) (k : Nat) (h : a ≡ b [MOD n]) :
    a ^ k ≡ b ^ k [MOD n] := by
  /-
  Theorem: Every natural-number power preserves congruence.
  Proof: We use induction on k, including zero.

  Base case: When k = 0, both powers are 1. We have already shown
  that every integer is congruent to itself.

  Inductive case: Suppose a ^ k is congruent to b ^ k modulo n.
  We also know that a is congruent to b modulo n. Multiplying these
  congruences gives

    a ^ k * a ≡ b ^ k * b [MOD n].

  These products are a ^ (k + 1) and b ^ (k + 1), as required.

  QED
  -/
  induction k with
  | zero =>
    rw [Int.pow_zero, Int.pow_zero]
    exact modeq_refl 1 n h.1
  | succ k ih =>
    exact modeq_pow_step a b n k h ih

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

theorem repeated_powers (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ i j : Nat, 0 < i ∧ i < j ∧ Congruent (a^i) (a^j) n := by
  /-
  Theorem: Two distinct positive powers of any integer are congruent
  modulo a positive n.
  Proof: Label the n+1 powers a^1 through a^(n+1) by their canonical
  remainders. If no two powers were congruent, all these labels
  would be distinct. They lie in the list 0 through n-1, which
  has only n entries. The elementary bound for distinct lists
  would then give n+1≤n, a contradiction. QED
  -/
  apply Classical.byContradiction
  intro hnot
  let f : Nat → Nat := fun i => canonicalLabel (a^(i+1)) n
  have hinj : ∀ i j : Nat, f i=f j → i=j := by
    intro i j he
    have hc := (canonicalLabel_eq_iff (a^(i+1)) (a^(j+1)) n hn).mp he
    by_cases hij : i < j
    · exact False.elim (hnot ⟨i+1,j+1,by omega,by omega,hc⟩)
    · by_cases hji : j < i
      · exact False.elim (hnot ⟨j+1,i+1,by omega,by omega,
          modeq_symm _ _ n hc⟩)
      · omega
  have hnd : ((List.range (n+1)).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp (R := fun i j : Nat => i ≠ j) ?_ (List.nodup_range _)
    intro i j hij he
    exact hij (hinj i j he)
  have hsub : ∀ r ∈ (List.range (n+1)).map f, r ∈ List.range n := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i,_,he⟩
    subst r
    exact List.mem_range.mpr (canonicalLabel_spec (a^(i+1)) n hn).1
  have hb := distinct_length_bound _ _ hnd hsub
  simp only [List.length_map,List.length_range] at hb
  omega

theorem coprime_power (a n : Int) (hn : 0 < n) (hcop : gcd a n=1) (j : Nat) :
    gcd (a^j) n=1 := by
  /-
  Theorem: Every nonnegative power of a number relatively prime
  to n remains relatively prime to n.
  Proof: Bezout gives a*u+n*v=1. We prove by induction that n and
  a^j have a linear combination equal to one. For j=0, a^0=1.
  At the induction step, combine the identities for n with a^j
  and with a to get an identity for n with a^j*a. Reorder its
  terms and use the preceding lemma to identify the gcd as one.
  This proof permits all integer bases, extending the positive-base
  statement, and also includes exponent zero. QED
  -/
  rcases bezout a n with ⟨u,v,he⟩
  rw [hcop] at he
  have hb : ∃ s t : Int, n*s+a*t=1 := ⟨v,u,by omega⟩
  have hp : ∀ k : Nat, ∃ s t : Int, n*s+a^k*t=1 := by
    intro k
    induction k with
    | zero => exact ⟨0,1,by simp [Int.pow_zero]⟩
    | succ k ih =>
      simpa only [Int.pow_succ] using bezout_product n (a^k) a ih hb
  rcases hp j with ⟨s,t,ht⟩
  exact gcd_one_right (a^j) n hn ⟨t,s,by omega⟩

theorem positive_power_one (a : Int) (n : Nat) (hn : 0 < n)
    (hcop : gcd a n=1) : ∃ k : Nat, 0 < k ∧ Congruent (a^k) 1 n := by
  /-
  Theorem: A number relatively prime to a positive modulus has
  a positive power congruent to one.
  Proof: Choose i<j with a^i congruent to a^j. Reverse this
  congruence and factor a^j=a^(j-i)*a^i. The power a^i is still
  relatively prime to n, so it can be cancelled. This leaves
  a^(j-i) congruent to one, and j-i is positive. QED
  -/
  rcases repeated_powers a n hn with ⟨i,j,_,hij,hc⟩
  have he : a^j=a^(j-i)*a^i := by
    rw [←power_add]
    congr 1
    omega
  have hrev := modeq_symm _ _ n hc
  rw [he] at hrev
  have hcancel : Congruent (a^(j-i)*a^i) (1*a^i) n := by simpa using hrev
  exact ⟨j-i,by omega,cancel_coprime (a^(j-i)) 1 (a^i) n
    (coprime_power a n (by omega) hcop i) hcancel⟩



/- Order is the least positive exponent returning to one. Outside
   the positive, coprime case we use zero solely to make it total. -/

noncomputable def reducedResidues (n : Nat) : List Nat := by
  exact ((List.range n).map (fun i => i+1)).filter (fun i => decide (gcd (i : Int) n=1))

theorem reduced_mem (n i : Nat) : i ∈ reducedResidues n ↔ 0 < i ∧ i ≤ n ∧ gcd (i : Int) n=1 := by
  /-
  Lemma: The reduced residue list consists exactly of the positive
  integers at most n that are coprime to n. Proof: Its initial
  list is 1,...,n; the filter keeps exactly the coprime entries.
  Its length defines the counting function phi, including n=1.
  QED
  -/
  simp only [reducedResidues,List.mem_filter,List.mem_map,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j,hj,he⟩,hc⟩
    exact ⟨by omega,by omega,hc⟩
  · rintro ⟨hi,hin,hc⟩
    exact ⟨⟨i-1,by omega,by omega⟩,hc⟩

noncomputable def phi (n : Nat) : Nat := (reducedResidues n).length

theorem phi_positive (n : Nat) (hn : 0 < n) : 0 < phi n := by
  /-
  Lemma: Phi of a positive integer is positive.
  Proof: One lies in the interval from one to n and is coprime
  to n, as the combination 1*1+n*0=1 shows. Thus at least this
  one representative is counted. QED
  -/
  have hc : gcd 1 (n : Int)=1 := gcd_one_right 1 n (by omega) ⟨1,0,by simp⟩
  have hm : 1 ∈ reducedResidues n := (reduced_mem n 1).mpr ⟨by omega,hn,hc⟩
  cases h : reducedResidues n with
  | nil => simp [h] at hm
  | cons a xs => simp only [phi,h,List.length_cons]; omega

def sumOn : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | d::ds, f => f d + sumOn ds f

theorem sum_on_le (ds : List Nat) (f g : Nat → Nat)
    (h : ∀ d ∈ ds, f d ≤ g d) : sumOn ds f ≤ sumOn ds g := by
  /-
  Lemma: Bounding each summand bounds the total.
  Proof: Add the bound for the first term to the bound supplied
  by induction for the remaining terms. QED
  -/
  induction ds with
  | nil => exact Nat.le_refl _
  | cons d ds ih =>
    have hfirst := h d (by simp)
    have hrest := ih (fun e he => h e (by simp [he]))
    simp only [sumOn]; omega

theorem equal_sum_forces_equal_terms (ds : List Nat) (f g : Nat → Nat)
    (hle : ∀ d ∈ ds, f d ≤ g d) (he : sumOn ds f=sumOn ds g) :
    ∀ d ∈ ds, f d=g d := by
  /-
  Lemma: If each term is bounded above and the totals are equal,
  every term attains its bound. Proof: The first term and the
  remaining sum are both bounded above. Equality of their sum
  forces equality in both bounds. Repeat on the remaining list.
  QED
  -/
  induction ds with
  | nil => intro d hd; simp at hd
  | cons a ds ih =>
    have hfirst := hle a (by simp)
    have htail : ∀ d ∈ ds, f d ≤ g d := fun d hd => hle d (by simp [hd])
    have hrest := sum_on_le ds f g htail
    simp only [sumOn] at he
    have hfirsteq : f a=g a := by omega
    have hresteq : sumOn ds f=sumOn ds g := by omega
    intro d hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d; exact hfirsteq
    · exact ih htail hresteq d hd

def positiveRange (n : Nat) : List Nat := (List.range n).map (fun i => i+1)

theorem positive_range_nodup (n : Nat) : (positiveRange n).Nodup := by
  /-
  Lemma: The positive range has no repetitions.
  Proof: Adding one to two different natural numbers cannot make
  them equal; the original range has no repetitions. QED
  -/
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp (R := fun i j : Nat => i ≠ j) ?_ (List.nodup_range n)
  intro i j h he
  exact h (by omega)

theorem positive_range_mem (n k : Nat) : k ∈ positiveRange n ↔ 0 < k ∧ k ≤ n := by
  /-
  Lemma: The positive range lists exactly the integers from one to n.
  Proof: Its entries are j+1 for 0≤j<n. Subtracting one gives the
  reverse correspondence. QED
  -/
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j,hj,hjk⟩
    have := List.mem_range.mp hj
    omega
  · intro h
    exact List.mem_map.mpr ⟨k-1,List.mem_range.mpr (by omega),by omega⟩

noncomputable def order (a : Int) (n : Nat) : Nat :=
  if h : 0 < n ∧ gcd a n=1 then
    Classical.choose (least_natural (fun k => 0 < k ∧ Congruent (a^k) 1 n)
      (positive_power_one a n h.1 h.2))
  else 0

noncomputable def orderClass (p d : Nat) : List Nat :=
  (positiveRange (p-1)).filter (fun a => decide (order (a : Int) p=d))

theorem order_class_mem (p d a : Nat) :
    a ∈ orderClass p d ↔ 0 < a ∧ a ≤ p-1 ∧ order (a : Int) p=d := by
  /-
  Lemma: The list for order d contains exactly the positive
  representatives below p with that order.
  Proof: Its filter tests the order equality on the positive
  interval ending at p-1. QED
  -/
  simp only [orderClass,List.mem_filter,decide_eq_true_eq,positive_range_mem]
  constructor
  · intro h; exact ⟨h.1.1,h.1.2,h.2⟩
  · intro h; exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩

theorem order_spec (a : Int) (n : Nat) (hn : 0 < n) (hcop : gcd a n=1) :
    0 < order a n ∧ Congruent (a^(order a n)) 1 n ∧
      ∀ k : Nat, 0 < k → Congruent (a^k) 1 n → order a n ≤ k := by
  /-
  Theorem: The order is positive, its power is congruent to one,
  and it is no larger than any other positive exponent with that
  property.
  Proof: The positive-power theorem makes the collection of such
  exponents nonempty. Well-ordering supplies a least member. The
  definition chooses that member, so it belongs to the collection
  and is at most every other member. QED

  Positivity is explicit because Lean's natural numbers include
  zero. No claim about the default value outside these hypotheses
  is needed to define order for the textbook's coprime inputs.
  -/
  have hs := Classical.choose_spec
    (least_natural (fun k => 0 < k ∧ Congruent (a^k) 1 n)
      (positive_power_one a n hn hcop))
  unfold order
  rw [dif_pos ⟨hn,hcop⟩]
  exact ⟨hs.1.1,hs.1.2,fun k hk hc => hs.2 k ⟨hk,hc⟩⟩

theorem powers_distinct (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1)
    (i j : Nat) (hi : 0 < i) (hij : i < j) (hj : j ≤ order a n) :
    ¬ Congruent (a^i) (a^j) n := by
  /-
  Theorem: The powers with exponents one through the order are
  pairwise incongruent. Proof: Suppose i<j in this range gave equal
  residues. Factor a^j=a^(j-i)*a^i and cancel the coprime factor
  a^i. Then a^(j-i) is congruent to one. But 0<j-i<order(a,n),
  contradicting the order's minimality. QED
  -/
  intro h
  have he : a^j=a^(j-i)*a^i := by
    rw [←power_add]
    congr 1
    omega
  have hr := modeq_symm _ _ n h
  rw [he] at hr
  have hp := cancel_coprime (a^(j-i)) 1 (a^i) n
    (coprime_power a n (by omega) hc i) (by simpa using hr)
  have hmin := (order_spec a n hn hc).2.2 (j-i) (by omega) hp
  omega

def cyclePowers (a : Int) (d : Nat) : List Int := (List.range d).map (fun j => a^(j+1))

theorem cycle_distinct (a : Int) (n : Nat) (hn : 0 < n) (ha : gcd a n=1) :
    (cyclePowers a (order a n)).Pairwise (fun r s => ¬ Congruent r s n) := by
  /-
  Lemma: The list a,a^2,...,a^d for d=ord(a) is pairwise
  incongruent. Proof: The exponents occur in strictly increasing
  order between one and d. Congruence of two such powers would
  contradict the minimal positive returning exponent. QED
  -/
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (order a n))
  intro i j hi hj hij
  simp only [List.mem_range] at hi hj
  exact powers_distinct a n hn ha (i+1) (j+1) (by omega) (by omega) (by omega)

def monomial : Nat → List Int
  | 0 => [1]
  | k+1 => 0 :: monomial k

theorem monomial_length (k : Nat) : (monomial k).length=k+1 := by
  /-
  Lemma: The coefficient list for x^k has length k+1.
  Proof: It starts with one coefficient. Each recursive step
  adds one zero to the front, increasing the length by one. QED
  -/
  induction k with
  | zero => rfl
  | succ k ih => simp only [monomial,List.length_cons,ih]

def leading : List Int → Int
  | [] => 0
  | [a] => a
  | _ :: b :: cs => leading (b :: cs)

theorem monomial_leading (k : Nat) : leading (monomial k)=1 := by
  /-
  Lemma: A monomial has leading coefficient one. Proof: The
  constant monomial is [1]. Adding a zero in front of a nonempty
  list leaves its final coefficient unchanged. Apply induction.
  QED
  -/
  induction k with
  | zero => rfl
  | succ k ih =>
    have hl := monomial_length k
    cases he : monomial k with
    | nil => rw [he] at hl; simp at hl
    | cons b cs => simpa only [monomial,he,leading] using ih

def evaluate : List Int → Int → Int
  | [], _ => 0
  | a :: cs, x => a+x*evaluate cs x

theorem monomial_evaluate (k : Nat) (x : Int) : evaluate (monomial k) x=x^k := by
  /-
  Lemma: A coefficient one preceded by k zeros represents x^k.
  Proof: At k=0 the polynomial is one. Each added zero shifts
  the coefficients by one position and multiplies the value by x.
  Induction therefore gives x^k. QED
  -/
  induction k with
  | zero => simp [monomial,evaluate,Int.pow_zero]
  | succ k ih => simp only [monomial,evaluate,Int.zero_add,ih,Int.pow_succ,Int.mul_comm]

def quotient (r : Int) : List Int → List Int
  | [] => []
  | [_] => []
  | _ :: b :: cs => evaluate (b :: cs) r :: quotient r (b :: cs)

theorem quotient_length (cs : List Int) (r : Int) (h : cs ≠ []) :
    (quotient r cs).length+1=cs.length := by
  /-
  Lemma: Dividing a nonempty coefficient list by x-r removes
  exactly one coefficient. Proof: A singleton has empty quotient.
  For a longer list the recursion adds one coefficient to the
  quotient of its tail. Apply induction to that nonempty tail.
  QED
  -/
  induction cs with
  | nil => exact False.elim (h rfl)
  | cons a cs ih =>
    cases cs with
    | nil => rfl
    | cons b cs =>
      have he := ih (by simp)
      simp only [quotient,List.length_cons]
      simp only [List.length_cons] at he
      omega

theorem quotient_leading (cs : List Int) (r : Int) (h : 2 ≤ cs.length) :
    leading (quotient r cs)=leading cs := by
  /-
  Lemma: The quotient of a positive-degree polynomial by x-r has
  the same leading coefficient. Proof: For a linear polynomial,
  the quotient is its leading coefficient. For a longer list,
  both leading coefficients lie in the corresponding tails.
  Apply induction. Thus a nonzero leading coefficient cannot
  disappear in synthetic division. QED
  -/
  induction cs with
  | nil => simp at h
  | cons a cs ih =>
    cases cs with
    | nil => simp at h
    | cons b cs =>
      cases cs with
      | nil => simp [quotient,evaluate,leading]
      | cons c cs =>
        have he := ih (by simp)
        simpa only [quotient,leading] using he

theorem division_identity (cs : List Int) (r x : Int) :
    evaluate cs x=(x-r)*evaluate (quotient r cs) x+evaluate cs r := by
  /-
  Lemma: Dividing an integer polynomial f by x-r leaves remainder
  f(r). Coefficient lists run from the constant term upward.
  Proof: Use induction on the coefficient list. Constants have
  zero quotient. Write the next polynomial as a+x*h(x). If
  h(x)=(x-r)*q(x)+h(r), then

    a+x*h(x)=(x-r)*(h(r)+x*q(x))+(a+r*h(r)).

  The last term is f(r), and h(r)+x*q(x) is the quotient given
  by the recursion. All its coefficients are integers. QED
  -/
  induction cs with
  | nil => simp [evaluate,quotient]
  | cons a cs ih =>
    cases cs with
    | nil => simp [evaluate,quotient]
    | cons b cs =>
      change a+x*evaluate (b::cs) x =
        (x-r)*(evaluate (b::cs) r+x*evaluate (quotient r (b::cs)) x)+
          (a+r*evaluate (b::cs) r)
      rw [ih]
      simp only [Int.mul_add,Int.add_mul,Int.sub_mul,Int.mul_sub,
        Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
      omega

theorem prime_product_divides (p : Nat) (a b : Int) (hp : Prime p)
    (h : (p : Int) ∣ a*b) : (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  /-
  Lemma: If a prime divides a product, it divides a factor.
  Proof: If it does not divide a, then a is coprime to p.
  Cancel a from b*a congruent to zero to obtain b congruent to
  zero. This says p divides b. QED
  -/
  by_cases ha : (p : Int) ∣ a
  · exact Or.inl ha
  · have hc := prime_coprime a p hp ha
    have hm : Congruent (b*a) (0*a) p := by
      refine ⟨by have := hp.1; omega,?_⟩
      simpa [Int.mul_comm] using h
    have hb := cancel_coprime b 0 a p hc hm
    exact Or.inr (by simpa using hb.2)

theorem quotient_root (cs : List Int) (r s : Int) (p : Nat) (hp : Prime p)
    (hr : (p : Int) ∣ evaluate cs r) (hs : (p : Int) ∣ evaluate cs s)
    (hne : ¬ Congruent r s p) : (p : Int) ∣ evaluate (quotient r cs) s := by
  /-
  Lemma: Removing a root r leaves every incongruent root s as a
  root of the quotient modulo p. Proof: The division identity is

    f(s)-f(r)=(s-r)*g(s).

  The prime divides both values on the left, hence their difference.
  A prime dividing a product divides a factor. It cannot divide
  s-r, since the two roots are incongruent. Therefore it divides
  g(s), as required. QED
  -/
  have hd := dvd_linear p (evaluate cs s) (evaluate cs r) 1 (-1) hs hr
  have he := division_identity cs r s
  have hid : evaluate cs s*1+evaluate cs r*(-1)=(s-r)*evaluate (quotient r cs) s := by
    simp only [Int.mul_one,Int.mul_neg]
    omega
  rw [hid] at hd
  rcases prime_product_divides p (s-r) (evaluate (quotient r cs) s) hp hd with h | h
  · exact False.elim (hne (modeq_symm s r p ⟨by have := hp.1; omega,h⟩))
  · exact h

theorem root_count (cs : List Int) (p : Nat) (hp : Prime p)
    (hl : ¬ (p : Int) ∣ leading cs) (roots : List Int)
    (hdist : roots.Pairwise (fun r s => ¬ Congruent r s p))
    (hroots : ∀ r ∈ roots, (p : Int) ∣ evaluate cs r) :
    roots.length ≤ cs.length-1 := by
  /-
  Lemma: A list of pairwise incongruent roots has at most one
  fewer entries than the coefficient list, provided the prime
  does not divide the leading coefficient.
  Proof: Induct on the length of the coefficient list. An empty
  list has leading coefficient zero, so is excluded. A nonzero
  constant modulo p has no root. Otherwise choose the first root
  r and divide by x-r. Every remaining root is a root of the
  quotient, since it is incongruent to r. The quotient has one
  fewer coefficient and the same leading coefficient. Induction
  bounds the remaining roots by the smaller degree. Restoring r
  adds one and gives the required bound. QED
  -/
  generalize hk : cs.length=k
  induction k using Nat.strongRecOn generalizing cs roots with
  | ind k ih =>
    cases roots with
    | nil => simp
    | cons r rs =>
      have hr := hroots r (by simp)
      have hpair := List.pairwise_cons.mp hdist
      have hdeg : 2 ≤ cs.length := by
        cases cs with
        | nil => exact False.elim (hl ⟨0,by simp [leading]⟩)
        | cons a tail =>
          cases tail with
          | nil =>
            have ha : (p : Int) ∣ a := by simpa [evaluate] using hr
            exact False.elim (hl ha)
          | cons b tail => simp
      have hlen := quotient_length cs r (by intro he; subst cs; simp at hdeg)
      have hlead : ¬ (p : Int) ∣ leading (quotient r cs) := by
        rw [quotient_leading cs r hdeg]
        exact hl
      have hrest : ∀ s ∈ rs, (p : Int) ∣ evaluate (quotient r cs) s := by
        intro s hs
        exact quotient_root cs r s p hp hr (hroots s (by simp [hs])) (hpair.1 s hs)
      have hb := ih (quotient r cs).length (by omega) (quotient r cs) hlead rs hpair.2 hrest rfl
      simp only [List.length_cons]
      omega

theorem power_root_count (p d : Nat) (hp : Prime p) (hd : 0 < d) (xs : List Int)
    (hpair : xs.Pairwise (fun r s => ¬ Congruent r s p))
    (hroot : ∀ x ∈ xs, Congruent (x^d) 1 p) : xs.length ≤ d := by
  /-
  Lemma: At most d incongruent integers satisfy x^d=1 modulo p.
  Proof: Use the coefficient list [-1,0,...,0,1] for x^d-1.
  It has d+1 coefficients and leading coefficient one, which
  the prime cannot divide. Each given solution is a root of this
  polynomial. The elementary polynomial root bound applies. QED
  -/
  let cs : List Int := -1 :: monomial (d-1)
  have hlen : cs.length=d+1 := by simp only [cs,List.length_cons,monomial_length]; omega
  have hlead : leading cs=1 := by
    have hl := monomial_length (d-1)
    cases he : monomial (d-1) with
    | nil => rw [he] at hl; simp at hl
    | cons b tail =>
      change leading (-1::monomial (d-1))=1
      rw [he]
      change leading (b::tail)=1
      rw [← he]
      exact monomial_leading (d-1)
  have hnot : ¬ (p : Int) ∣ leading cs := by
    rw [hlead]
    intro h
    have hb := divisor_le_positive p 1 (by decide) h
    have := hp.1
    omega
  have heval : ∀ x, evaluate cs x=x^d-1 := by
    intro x
    change -1+x*evaluate (monomial (d-1)) x=x^d-1
    rw [monomial_evaluate,Int.mul_comm x (x^(d-1)),← Int.pow_succ]
    have he : d-1+1=d := by omega
    rw [he]
    omega
  have hb := root_count cs p hp hnot xs hpair (by
    intro x hx
    rw [heval]
    exact (hroot x hx).2)
  rw [hlen] at hb
  omega

theorem power_multiple_one (a : Int) (n k q : Nat)
    (hk : Congruent (a^k) 1 n) : Congruent (a^(k*q)) 1 n := by
  /-
  Lemma: If a^k is congruent to one, so is a^(k*q) for every
  nonnegative q. Proof: Induct on q. The zero power is one.
  Each successor adds k to the exponent, so the power is multiplied
  by a^k. Multiplying the two congruences to one proves the step.
  QED
  -/
  induction q with
  | zero => simpa [Int.pow_zero] using modeq_refl 1 n hk.1
  | succ q ih =>
    rw [Nat.mul_succ,power_add]
    simpa using modeq_mult _ 1 _ 1 n ih hk

theorem cycle_power_one (a : Int) (n : Nat) (hn : 0 < n) (ha : gcd a n=1)
    (x : Int) (hx : x ∈ cyclePowers a (order a n)) : Congruent (x^(order a n)) 1 n := by
  /-
  Lemma: Every power in the cycle solves x^d=1, where d is the
  order. Proof: Write x=a^(j+1). Raising it to d gives a power
  whose exponent d*(j+1) is a multiple of the order. QED
  -/
  rcases List.mem_map.mp hx with ⟨j,_,he⟩
  subst x
  rw [power_mul,Nat.mul_comm (j+1) (order a n)]
  exact power_multiple_one a n (order a n) (j+1) (order_spec a n hn ha).2.1

theorem power_root_in_cycle (a x : Int) (p : Nat) (hp : Prime p) (ha : gcd a p=1)
    (hx : Congruent (x^(order a p)) 1 p) :
    ∃ i : Nat, 0 < i ∧ i ≤ order a p ∧ Congruent x (a^i) p := by
  /-
  Lemma: Every solution of x^d=1 is congruent to a power of an
  element a of order d. Proof: The d cycle powers are distinct
  solutions. If x were incongruent to all of them, adjoining x
  would give d+1 incongruent solutions. The power root bound
  excludes this. Hence x matches one of the powers a through a^d.
  QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hd := (order_spec a p hn ha).1
  apply Classical.byContradiction
  intro hnone
  have hsep : ∀ y ∈ cyclePowers a (order a p), ¬ Congruent x y p := by
    intro y hy hxy
    rcases List.mem_map.mp hy with ⟨j,hj,he⟩
    have hjb := List.mem_range.mp hj
    apply hnone
    exact ⟨j+1,by omega,by omega,by simpa only [he] using hxy⟩
  have hpair := List.pairwise_cons.mpr ⟨hsep,cycle_distinct a p hn ha⟩
  have hb := power_root_count p (order a p) hp hd (x::cyclePowers a (order a p)) hpair (by
    intro y hy
    rcases List.mem_cons.mp hy with he | hy
    · subst y; exact hx
    · exact cycle_power_one a p hn ha y hy)
  simp only [cyclePowers,List.length_cons,List.length_map,List.length_range] at hb
  omega

theorem congruent_orders (a b : Int) (n : Nat) (hn : 0 < n)
    (ha : gcd a n=1) (hb : gcd b n=1) (h : Congruent a b n) : order a n=order b n := by
  /-
  Lemma: Congruent coprime integers have the same order.
  Proof: Congruent inputs have congruent powers. Thus each positive
  exponent returning one input to one also returns the other.
  Minimality bounds each order by the other, so they are equal.
  QED
  -/
  have hs := order_spec a n hn ha
  have ht := order_spec b n hn hb
  have h1 := hs.2.2 _ ht.1 (modeq_trans _ _ _ n (modeq_pow a b n (order b n) h) ht.2.1)
  have h2 := ht.2.2 _ hs.1 (modeq_trans _ _ _ n
    (modeq_pow b a n (order a n) (modeq_symm _ _ n h)) hs.2.1)
  omega

theorem equal_power_order_coprime (a : Int) (n i : Nat) (hn : 0 < n)
    (ha : gcd a n=1) (he : order (a^i) n=order a n) : gcd (i : Int) (order a n)=1 := by
  /-
  Lemma: If a^i has the full order d of a, then i is coprime
  to d. Proof: Let g=gcd(i,d), and write i=g*u and d=g*v.
  Since d>0, both g and v are positive. The identity i*v=d*u
  makes (a^i)^v congruent to one. Its order d is therefore at
  most v. But d=g*v, so g cannot exceed one. Thus g=1. QED
  -/
  have hs := order_spec a n hn ha
  have ht := order_spec (a^i) n hn (coprime_power a n (by omega) ha i)
  let d := order a n
  let g := (gcd (i : Int) d).toNat
  have hgdata := gcd_data (i : Int) d
  have hgcast : (g : Int)=gcd (i : Int) d := Int.toNat_of_nonneg hgdata.1
  have hgpositive := gcd_positive (i : Int) d (Or.inr (by dsimp [d]; omega))
  have hgpos : 0 < g := by omega
  have hgi : g ∣ i := Int.ofNat_dvd.mp (by rw [hgcast]; exact hgdata.2.1)
  have hgd : g ∣ d := Int.ofNat_dvd.mp (by rw [hgcast]; exact hgdata.2.2.1)
  rcases hgi with ⟨u,hu⟩
  rcases hgd with ⟨v,hv⟩
  have hvpos : 0 < v := by
    by_cases hz : v=0
    · rw [hz,Nat.mul_zero] at hv
      dsimp [d] at hv
      omega
    · omega
  have hmul : i*v=d*u := by
    rw [hu,hv]
    simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
  have hm := power_multiple_one a n d u hs.2.1
  have hreturn : Congruent ((a^i)^v) 1 n := by rw [power_mul,hmul]; exact hm
  have hbound := ht.2.2 v hvpos hreturn
  rw [he] at hbound
  have hg1 : g=1 := by
    by_cases h : g=1
    · exact h
    · have h2 := Nat.mul_le_mul_right v (by omega : 2 ≤ g)
      change d ≤ v at hbound
      omega
  rw [hg1] at hgcast
  exact hgcast.symm

theorem equal_order_index (a b : Int) (p : Nat) (hp : Prime p)
    (ha : gcd a p=1) (hb : gcd b p=1) (he : order b p=order a p) :
    ∃ i : Nat, 0 < i ∧ i ≤ order a p ∧ gcd (i : Int) (order a p)=1 ∧ Congruent b (a^i) p := by
  /-
  Lemma: Every element with the same order d as a is represented
  by a power a^i with 1≤i≤d and gcd(i,d)=1. Proof: Its d-th
  power is one, so the full cycle exhausts the possible roots
  and supplies i. Congruence preserves order, so a^i has order d.
  The preceding necessity argument makes i coprime to d. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hroot : Congruent (b^(order a p)) 1 p := by
    rw [← he]
    exact (order_spec b p hn hb).2.1
  rcases power_root_in_cycle a b p hp ha hroot with ⟨i,hi,hid,hbi⟩
  have horder := congruent_orders b (a^i) p hn hb (coprime_power a p (by omega) ha i) hbi
  have hcop := equal_power_order_coprime a p i hn ha (horder.symm.trans he)
  exact ⟨i,hi,hid,hcop,hbi⟩

theorem order_count (p d : Nat) (hp : Prime p) (xs : List Int)
    (hpair : xs.Pairwise (fun a b => ¬ Congruent a b p))
    (horders : ∀ a ∈ xs, gcd a p=1 ∧ order a p=d) : xs.length ≤ phi d := by
  /-
  Theorem: At most phi(d) incongruent integers have order d modulo
  a prime. Proof: If the list is empty, there is nothing to count.
  Otherwise fix its first element a. Each element b is congruent
  to a^i for some 1≤i≤d coprime to d. Choose such an exponent
  for each b. Two elements assigned the same exponent would be
  congruent, which is excluded. Thus the chosen exponents form a
  distinct list drawn from the reduced representatives counted
  by phi(d). The elementary distinct-list bound gives the result.
  Coprimality makes the order meaningful; d=0 consequently admits
  no such elements, and is harmless in this formulation. QED
  -/
  cases xs with
  | nil => exact Nat.zero_le _
  | cons a xs =>
    have ha := horders a (by simp)
    have hspec : ∀ b ∈ a::xs, ∃ i : Nat, 0 < i ∧ i ≤ d ∧ gcd (i : Int) d=1 ∧ Congruent b (a^i) p := by
      intro b hb
      have hs := horders b hb
      have he := equal_order_index a b p hp ha.1 hs.1 (hs.2.trans ha.2.symm)
      simpa only [ha.2] using he
    let index (b : Int) : Nat := if h : b ∈ a::xs then Classical.choose (hspec b h) else 0
    have hindex : ∀ b (_hb : b ∈ a::xs),
        0 < index b ∧ index b ≤ d ∧ gcd (index b : Int) d=1 ∧ Congruent b (a^(index b)) p := by
      intro b hb
      dsimp only [index]
      rw [dif_pos hb]
      exact Classical.choose_spec (hspec b hb)
    have hnd : ((a::xs).map index).Nodup := by
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem ?_ hpair
      intro b c hb hc hbc he
      have hs := (hindex b hb).2.2.2
      have ht := (hindex c hc).2.2.2
      rw [he] at hs
      exact hbc (modeq_trans _ _ _ p hs (modeq_symm _ _ p ht))
    have hsub : ∀ i ∈ (a::xs).map index, i ∈ reducedResidues d := by
      intro i hi
      rcases List.mem_map.mp hi with ⟨b,hb,he⟩
      subst i
      have hs := hindex b hb
      exact (reduced_mem d _).mpr ⟨hs.1,hs.2.1,hs.2.2.1⟩
    have hb := distinct_length_bound _ _ hnd hsub
    change (a::xs).length ≤ (reducedResidues d).length
    simpa only [List.length_map] using hb

theorem order_class_bound (p d : Nat) (hp : Prime p) :
    (orderClass p d).length ≤ phi d := by
  /-
  Lemma: The number of representatives of order d is at most
  phi(d). Proof: The selected representatives are distinct and
  lie between one and p-1, so equality of their residue classes
  would be equality of the representatives. They are coprime to
  the prime p. The elementary power-cycle bound therefore applies.
  QED
  -/
  have hnd : (orderClass p d).Nodup := (positive_range_nodup (p-1)).filter _
  have hpair : ((orderClass p d).map (fun a : Nat => (a : Int))).Pairwise
      (fun a b => ¬ Congruent a b p) := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ hnd
    intro a b ha hb hab he
    have ha' := (order_class_mem p d a).mp ha
    have hb' := (order_class_mem p d b).mp hb
    have heq := bounded_congruent_equal a b p (by omega) (by have := hp.1; omega)
      (by omega) (by have := hp.1; omega) he
    exact hab (by omega)
  have h := order_count p d hp ((orderClass p d).map (fun a : Nat => (a : Int))) hpair (by
    intro a ha
    rcases List.mem_map.mp ha with ⟨b,hb,hba⟩
    subst a
    have hb' := (order_class_mem p d b).mp hb
    exact ⟨small_prime_coprime p b hp hb'.1 (by have := hp.1; omega),hb'.2.2⟩)
  simpa only [List.length_map] using h

theorem sum_on_zero (ds : List Nat) : sumOn ds (fun _ => 0)=0 := by
  /-
  Lemma: A sum of zeros is zero.
  Proof: Induction adds one zero at a time. QED
  -/
  induction ds with
  | nil => rfl
  | cons _d ds ih => simp only [sumOn,ih,Nat.zero_add]

theorem sum_on_congr (ds : List Nat) (f g : Nat → Nat)
    (h : ∀ d ∈ ds, f d=g d) : sumOn ds f=sumOn ds g := by
  /-
  Lemma: Equal summands give equal finite sums.
  Proof: Match the first summands, then apply induction to the
  remaining list. QED
  -/
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [sumOn,h d (by simp),ih (fun e he => h e (by simp [he]))]

theorem sum_on_add (ds : List Nat) (f g : Nat → Nat) :
    sumOn ds (fun d => f d+g d)=sumOn ds f+sumOn ds g := by
  /-
  Lemma: A sum of pairwise sums separates into the two sums.
  Proof: Expand the first summands and use induction. Associating
  and commuting addition puts the f and g terms together. QED
  -/
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [sumOn,ih]; omega

theorem sum_single_label (ds : List Nat) (a : Nat) (hnd : ds.Nodup)
    (ha : a ∈ ds) : sumOn ds (fun d => if a=d then 1 else 0)=1 := by
  /-
  Lemma: Marking one label in a list without repetitions gives
  total one. Proof: If the first label is a, all remaining marks
  are zero. Otherwise its mark is zero and induction counts the
  unique occurrence in the rest of the list. QED
  -/
  induction ds with
  | nil => simp at ha
  | cons d ds ih =>
    have hpair := List.pairwise_cons.mp hnd
    by_cases he : a=d
    · subst a
      have hz : sumOn ds (fun e => if d=e then 1 else 0)=0 := by
        rw [sum_on_congr ds _ (fun _ => 0) (by
          intro e he
          exact if_neg (hpair.1 e he)),sum_on_zero]
      simp [sumOn,hz]
    · have ham : a ∈ ds := by rcases List.mem_cons.mp ha with h | h; exact False.elim (he h); exact h
      simp only [sumOn,if_neg he,Nat.zero_add,ih hpair.2 ham]

theorem count_by_labels (xs ds : List Nat) (f : Nat → Nat)
    (hnd : ds.Nodup) (hlabels : ∀ x ∈ xs, f x ∈ ds) :
    sumOn ds (fun d => (xs.filter (fun x => decide (f x=d))).length)=xs.length := by
  /-
  Lemma: Sorting a finite list into distinct labels counts each
  entry exactly once, provided every entry has a listed label.
  Proof: Remove the first entry x. Its addition increases exactly
  the count for f(x) by one. The sum of those increases is one,
  and induction counts all remaining entries. QED
  -/
  induction xs with
  | nil => simpa only [List.filter_nil,List.length_nil] using sum_on_zero ds
  | cons x xs ih =>
    have hstep : ∀ d ∈ ds,
        ((x::xs).filter (fun y => decide (f y=d))).length=
          (if f x=d then 1 else 0)+(xs.filter (fun y => decide (f y=d))).length := by
      intro d _
      by_cases he : f x=d
      · simp [he,Nat.add_comm]
      · simp [he]
    rw [sum_on_congr ds _ _ hstep,sum_on_add,
      sum_single_label ds (f x) hnd (hlabels x (by simp)),
      ih (fun y hy => hlabels y (by simp [hy]))]
    simp only [List.length_cons]; omega

def divisors (n : Nat) : List Nat := (positiveRange n).filter (fun d => decide (d ∣ n))

theorem divisors_nodup (n : Nat) : (divisors n).Nodup := by
  /-
  Lemma: Each divisor is listed only once.
  Proof: Filtering a list without repetitions cannot introduce one.
  QED
  -/
  exact (positive_range_nodup n).filter _

theorem divisors_mem (n d : Nat) (hn : 0 < n) :
    d ∈ divisors n ↔ 0 < d ∧ d ∣ n := by
  /-
  Lemma: Our divisor list contains precisely the positive divisors.
  Proof: A positive divisor of positive n is at most n, so filtering
  the interval from one to n loses no divisor. QED
  -/
  simp only [divisors,List.mem_filter,decide_eq_true_eq,positive_range_mem]
  constructor
  · intro h; exact ⟨h.1.1,h.2⟩
  · intro h; exact ⟨⟨h.1,Nat.le_of_dvd hn h.2⟩,h.2⟩

theorem power_remainder (a : Int) (n : Nat) (hn : 0 < n)
    (hc : gcd a n=1) (m : Nat) :
    Congruent (a^m) (a^(m % order a n)) n := by
  /-
  Lemma: Dividing an exponent by the order does not change its
  power's congruence class when the exponent is replaced by its
  remainder. Proof: Put k=order(a,n). Division gives m=r+k*q.
  The power a^(k*q) is congruent to one, so
  a^m=a^r*a^(k*q) is congruent to a^r. QED
  -/
  have hs := order_spec a n hn hc
  have hp := power_multiple_one a n (order a n) (m / order a n) hs.2.1
  have he := Nat.mod_add_div m (order a n)
  have h := modeq_mult (a^(m % order a n)) (a^(m % order a n))
    (a^(order a n*(m / order a n))) 1 n
    (modeq_refl _ _ (by omega)) hp
  rw [←power_add,he,Int.mul_one] at h
  exact h

theorem order_dvd_iff (a : Int) (n : Nat) (hn : 0 < n)
    (hc : gcd a n=1) (m : Nat) :
    Congruent (a^m) 1 n ↔ order a n ∣ m := by
  /-
  Theorem: A power is congruent to one exactly when the order
  divides its exponent. Proof: Divide m by k=order(a,n), leaving
  remainder r<k. The remainder-power lemma shows that a^r is
  congruent to one if a^m is. If r were positive, minimality of k
  would give k≤r, a contradiction. Thus r=0 and k divides m.
  Conversely, a multiple of the returning exponent k returns to
  one by the multiplication lemma. QED
  -/
  have hs := order_spec a n hn hc
  constructor
  · intro hm
    have hr := modeq_trans _ _ _ n (modeq_symm _ _ n (power_remainder a n hn hc m)) hm
    have hlt := Nat.mod_lt m hs.1
    have hz : m % order a n=0 := by
      by_cases hpos : 0 < m % order a n
      · have hmin := hs.2.2 _ hpos hr
        omega
      · omega
    refine ⟨m / order a n,?_⟩
    have he := Nat.mod_add_div m (order a n)
    omega
  · rintro ⟨q,rfl⟩
    exact power_multiple_one a n (order a n) q hs.2.1

end NumberTheory.ResidueSigns
