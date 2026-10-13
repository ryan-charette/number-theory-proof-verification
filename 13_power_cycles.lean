import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PowerCycles

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



theorem gcd_greatest (a b : Int) (h : a ≠ 0 ∨ b ≠ 0)
    (e : Int) (ha : e ∣ a) (hb : e ∣ b) : e ≤ gcd a b := by
  /-
  Theorem: Every common divisor is at most the constructed gcd.
  Proof: A common divisor divides every integer linear combination,
  hence divides the gcd by its Euclidean representation. Since the
  gcd is positive, the preceding bound gives the result. QED
  -/
  rcases (gcd_data a b).2.2.2 with ⟨x, y, hxy⟩
  have hd := dvd_linear e a b x y ha hb
  rw [hxy] at hd
  exact divisor_le_positive e (gcd a b) (gcd_positive a b h) hd



theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The gcd of two integers is an integer linear combination.
  Proof: These are the coefficients constructed by the Euclidean
  procedure and back-substitution above. The construction also covers
  the harmless extra case a = b = 0. QED
  -/
  exact (gcd_data a b).2.2.2



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



def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a-b

local notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

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

noncomputable def order (a : Int) (n : Nat) : Nat :=
  if h : 0 < n ∧ gcd a n=1 then
    Classical.choose (least_natural (fun k => 0 < k ∧ Congruent (a^k) 1 n)
      (positive_power_one a n h.1 h.2))
  else 0

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


theorem power_cycle (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1)
    (m : Nat) : ∃ i : Nat, 0 < i ∧ i ≤ order a n ∧ Congruent (a^m) (a^i) n := by
  /-
  Theorem: Every power is congruent to one of the powers with
  exponents one through the order. Proof: Reduce m to its remainder
  r modulo the order k. If r>0, choose r, which is less than k.
  If r=0, the power is congruent to one; choose k itself, whose
  power is also congruent to one. QED
  -/
  have hs := order_spec a n hn hc
  have hr := power_remainder a n hn hc m
  by_cases hz : m % order a n=0
  · rw [hz,Int.pow_zero] at hr
    exact ⟨order a n,hs.1,Nat.le_refl _,
      modeq_trans _ _ _ n hr (modeq_symm _ _ n hs.2.1)⟩
  · have hlt := Nat.mod_lt m hs.1
    exact ⟨m % order a n,by omega,by omega,hr⟩


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


theorem order_lt_modulus (a : Int) (n : Nat) (hn : 1 < n) (hc : gcd a n=1) :
    order a n < n := by
  /-
  Theorem: The order is less than the modulus when n>1.
  Proof: Label the powers from a^1 through a^k, where k is the
  order, by their canonical remainders. Distinct powers in this
  range have distinct labels. None has label zero, since powers
  remain coprime to n. Thus the k distinct labels lie among the
  n-1 nonzero canonical remainders. Counting gives k≤n-1. QED

  The hypothesis n>1 corrects the exceptional modulus one: there
  the least positive returning exponent is one, so a strict bound
  by the modulus would be false.
  -/
  let f : Nat → Nat := fun i => canonicalLabel (a^(i+1)) n
  have hnd : ((List.range (order a n)).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ (List.nodup_range _)
    intro i j hi hj hne he
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    have hp := (canonicalLabel_eq_iff (a^(i+1)) (a^(j+1)) n (by omega)).mp he
    by_cases hij : i < j
    · exact powers_distinct a n (by omega) hc (i+1) (j+1) (by omega) (by omega) (by omega) hp
    · exact powers_distinct a n (by omega) hc (j+1) (i+1) (by omega) (by omega) (by omega)
        (modeq_symm _ _ n hp)
  have hsub : ∀ r ∈ (List.range (order a n)).map f, r ∈ (List.range n).erase 0 := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i,_,he⟩
    subst r
    have hs := canonicalLabel_spec (a^(i+1)) n (by omega)
    have hz : f i ≠ 0 := by
      intro hzero
      have hz' : canonicalLabel (a^(i+1)) n=0 := hzero
      rw [hz'] at hs
      exact coprime_not_zero (a^(i+1)) n hn
        (coprime_power a n (by omega) hc (i+1)) hs.2
    exact (List.mem_erase_of_ne hz).mpr (List.mem_range.mpr hs.1)
  have hb := distinct_length_bound _ _ hnd hsub
  have he := List.length_erase_of_mem (by simp; omega : 0 ∈ List.range n)
  simp only [List.length_map,List.length_range] at hb he
  omega


def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d=1 ∨ d=p

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


theorem shifted_labels_injective (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1)
    (i j : Nat) (hi : i < n) (hj : j < n)
    (he : canonicalLabel (((i+1 : Nat) : Int)*a) n=
      canonicalLabel (((j+1 : Nat) : Int)*a) n) : i=j := by
  /-
  Lemma: The n multiples a through n*a have distinct residue
  labels. Proof: Equal labels allow cancellation of a. Subtracting
  one from the two resulting representatives gives congruent
  integers i and j between zero and n-1, hence equal integers. QED
  -/
  have h := cancel_coprime ((i+1 : Nat) : Int) ((j+1 : Nat) : Int) a n hc
    ((canonicalLabel_eq_iff _ _ n hn).mp he)
  have hd : Congruent (i : Int) j n := by
    rcases h with ⟨hp,q,hq⟩
    exact ⟨hp,q,by omega⟩
  have hb := bounded_congruent_equal i j n (by omega) (by omega)
    (by omega) (by omega) hd
  omega



theorem multiples_complete (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1) :
    ∀ x : Int, ∃ i : Nat, 0 < i ∧ i ≤ n ∧ Congruent x ((i : Int)*a) n ∧
      ∀ j : Nat, 0 < j → j ≤ n → Congruent x ((j : Int)*a) n → j=i := by
  /-
  Theorem: The multiples a,2*a,...,n*a form a complete residue
  system when a is coprime to n; in particular this holds for a
  prime modulus and an integer not divisible by it.
  Proof: Their n labels are distinct and lie in the canonical list
  of n residues. They therefore rearrange that list. Every integer's
  label occurs, proving existence of a representative. Equal labels
  force equal indices by the preceding cancellation argument,
  proving uniqueness. QED
  -/
  let f : Nat → Nat := fun i => canonicalLabel (((i+1 : Nat) : Int)*a) n
  have hnd : ((List.range n).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ (List.nodup_range n)
    intro i j hi hj hne he
    exact hne (shifted_labels_injective a n hn hc i j
      (List.mem_range.mp hi) (List.mem_range.mp hj) he)
  have hs : ∀ r ∈ (List.range n).map f, r ∈ List.range n := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i,_,he⟩
    subst r
    exact List.mem_range.mpr (canonicalLabel_spec _ n hn).1
  have hp := distinct_subset_perm _ _ hnd hs (by simp)
  intro x
  have hx : canonicalLabel x n ∈ (List.range n).map f :=
    hp.mem_iff.mpr (List.mem_range.mpr (canonicalLabel_spec x n hn).1)
  rcases List.mem_map.mp hx with ⟨i,hi,he⟩
  have hib := List.mem_range.mp hi
  refine ⟨i+1,by omega,by omega,(canonicalLabel_eq_iff _ _ n hn).mp he.symm,?_⟩
  intro j hj hjn hjc
  have heq : f (j-1)=f i := by
    have hjid : j-1+1=j := by omega
    change canonicalLabel (((j-1+1 : Nat) : Int)*a) n= _
    rw [hjid]
    exact ((canonicalLabel_eq_iff _ _ n hn).mpr hjc).symm.trans he.symm
  have hij := shifted_labels_injective a n hn hc (j-1) i (by omega) hib heq
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



def intProduct : List Int → Int
  | [] => 1
  | a::xs => a*intProduct xs

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


theorem fermat_forms_equivalent (p : Nat) (hp : Prime p) :
    (∀ a : Int, gcd a p=1 → Congruent (a^(p-1)) 1 p) ↔
      (∀ a : Int, Congruent (a^p) a p) := by
  /-
  Theorem: The coprime and unrestricted forms of Fermat's theorem
  imply each other. Proof: From the coprime form, multiply by a
  when p does not divide a. If p divides a, both a and a^p are
  congruent to zero; factor a^p=a^(p-1)*a to see this directly.
  Conversely, for coprime a, factor a^p and cancel a from the
  unrestricted congruence a^p congruent to a. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have he : p-1+1=p := by omega
  have hpow : ∀ a : Int, a^p=a^(p-1)*a := by
    intro a
    rw [←Int.pow_succ,he]
  constructor
  · intro h a
    by_cases ha : (p : Int) ∣ a
    · have hz : Congruent a 0 p := ⟨by omega,by simpa using ha⟩
      have hm := modeq_mult (a^(p-1)) (a^(p-1)) a 0 p
        (modeq_refl _ _ (by omega)) hz
      rw [←hpow,Int.mul_zero] at hm
      exact modeq_trans _ _ _ p hm (modeq_symm _ _ p hz)
    · have hm := modeq_mult _ 1 a a p (h a (prime_coprime a p hp ha))
        (modeq_refl _ _ (by omega))
      simpa only [←hpow,Int.one_mul] using hm
  · intro h a hc
    have hm := h a
    rw [hpow] at hm
    exact cancel_coprime (a^(p-1)) 1 a p hc (by simpa using hm)

end NumberTheory.PowerCycles
