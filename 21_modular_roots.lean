import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ModularRoots

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

def intProduct : List Int → Int
  | [] => 1
  | a::xs => a*intProduct xs

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

noncomputable def positiveLabel (a : Int) (n : Nat) : Nat :=
  if canonicalLabel a n=0 then n else canonicalLabel a n

theorem positiveLabel_spec (a : Int) (n : Nat) (hn : 0 < n) :
    0 < positiveLabel a n ∧ positiveLabel a n ≤ n ∧ Congruent a (positiveLabel a n) n := by
  /-
  Lemma: Every integer has a positive representative at most n.
  Proof: Use its canonical label unless that label is zero. Replace
  zero by n, which is congruent to zero; otherwise the canonical
  bounds already give a positive representative below n. QED
  -/
  have hs := canonicalLabel_spec a n hn
  unfold positiveLabel
  by_cases hz : canonicalLabel a n=0
  · rw [if_pos hz]
    have hs0 : Congruent a 0 n := by simpa only [hz,Int.natCast_zero] using hs.2
    refine ⟨hn,Nat.le_refl _,modeq_trans a 0 n n hs0 ?_⟩
    exact ⟨by omega,-1,by simp⟩
  · rw [if_neg hz]
    exact ⟨by omega,by omega,hs.2⟩

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

noncomputable def gcd (a b : Int) : Int := (Classical.choose (euclid_integer a b) : Nat)

noncomputable def reducedResidues (n : Nat) : List Nat := by
  exact ((List.range n).map (fun i => i+1)).filter (fun i => decide (gcd (i : Int) n=1))

theorem reduced_nodup (n : Nat) : (reducedResidues n).Nodup := by
  /-
  Lemma: The reduced residue list has no repeated entries.
  Proof: The initial range is distinct, adding one preserves
  distinctness, and filtering can only remove entries. QED
  -/
  have h : ((List.range n).map (fun i => i+1)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp (R := fun i j : Nat => i ≠ j) ?_ (List.nodup_range n)
    intro i j hij he
    exact hij (by omega)
  exact h.filter _

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

theorem positive_congruent_equal (a b n : Int) (ha : 0 < a) (han : a ≤ n)
    (hb : 0 < b) (hbn : b ≤ n) (h : Congruent a b n) : a=b := by
  /-
  Lemma: Congruent representatives in the interval from one to n
  are equal. Proof: Subtract one from each. Their difference is
  unchanged, and both now lie between zero and n-1. The bounded
  remainder uniqueness theorem makes them equal. QED
  -/
  have hc : Congruent (a-1) (b-1) n := by
    rcases h with ⟨hn,q,hq⟩
    exact ⟨hn,q,by omega⟩
  have he := bounded_congruent_equal (a-1) (b-1) n (by omega) (by omega)
    (by omega) (by omega) hc
  omega

theorem reduced_multiples_distinct (a : Int) (n i j : Nat) (hc : gcd a n=1)
    (hi : i ∈ reducedResidues n) (hj : j ∈ reducedResidues n)
    (h : Congruent (a*i) (a*j) n) : i=j := by
  /-
  Theorem: Multiplying different reduced representatives by a
  coprime integer cannot make them congruent. Proof: Cancel a
  from the congruence. The two original positive representatives
  lie at most n, so uniqueness makes them equal. QED
  -/
  have hib := (reduced_mem n i).mp hi
  have hjb := (reduced_mem n j).mp hj
  have hcancel := cancel_coprime i j a n hc (by simpa only [Int.mul_comm] using h)
  have he := positive_congruent_equal i j n (by omega) (by omega) (by omega) (by omega) hcancel
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

theorem coprime_multiply (a b n : Int) (ha : gcd a n=1) (hb : gcd b n=1) : gcd (a*b) n=1 := by
  /-
  Theorem: Multiplying two integers relatively prime to n preserves
  that property. Proof: Reverse their Bezout identities, combine
  them over the product, and reverse the resulting identity to
  identify the gcd as one. The argument includes all integer n.
  QED
  -/
  rcases bezout a n with ⟨u,v,hu⟩
  rcases bezout b n with ⟨s,t,hs⟩
  rw [ha] at hu
  rw [hb] at hs
  rcases bezout_product n a b ⟨v,u,by omega⟩ ⟨t,s,by omega⟩ with ⟨x,y,he⟩
  exact gcd_one_combination (a*b) n ⟨y,x,by omega⟩

theorem reduced_labels_perm (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1) :
    ((reducedResidues n).map (fun i : Nat => positiveLabel ((i : Int)*a) n)).Perm (reducedResidues n) := by
  /-
  Lemma: Multiplication by a coprime integer rearranges the reduced
  residue labels. Proof: Each product remains coprime to n, and
  its positive label preserves coprimality, so the labels stay in
  the same list. Equal labels imply congruent products and hence
  equal original representatives by cancellation. The labels are
  therefore distinct and their number is unchanged, giving a
  rearrangement. QED
  -/
  let f : Nat → Nat := fun i => positiveLabel ((i : Int)*a) n
  have hnd : ((reducedResidues n).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ (reduced_nodup n)
    intro i j hi hj hne he
    have h₁ := (positiveLabel_spec ((i : Int)*a) n hn).2.2
    have h₂ := (positiveLabel_spec ((j : Int)*a) n hn).2.2
    change positiveLabel ((i : Int)*a) n=positiveLabel ((j : Int)*a) n at he
    rw [he] at h₁
    have hprod := modeq_trans _ _ _ n h₁ (modeq_symm _ _ n h₂)
    exact hne (reduced_multiples_distinct a n i j hc hi hj
      (by simpa only [Int.mul_comm] using hprod))
  apply distinct_subset_perm _ _ hnd ?_ (by simp)
  intro r hr
  rcases List.mem_map.mp hr with ⟨i,hi,he⟩
  subst r
  have hs := positiveLabel_spec ((i : Int)*a) n hn
  apply (reduced_mem n _).mpr
  exact ⟨hs.1,hs.2.1,congruent_coprime _ _ _
    (coprime_multiply i a n ((reduced_mem n i).mp hi).2.2 hc) hs.2.2⟩

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

noncomputable def phi (n : Nat) : Nat := (reducedResidues n).length

theorem euler_power (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1) :
    Congruent (a^(phi n)) 1 n := by
  /-
  Theorem: A coprime integer raised to phi(n) is congruent to one.
  Proof: Multiply all reduced representatives to obtain P. Their
  scaled product is a^phi(n)*P. Replacing the scaled entries by
  their labels preserves the product modulo n, and those labels
  rearrange the original list. Thus a^phi(n)*P is congruent to P.
  Every factor of P is coprime to n, so P is too. Cancel P. QED
  -/
  have hp := product_congruent (reducedResidues n) (fun i => (i : Int)*a)
    (fun i => (positiveLabel ((i : Int)*a) n : Int)) n (by omega)
    (fun i _ => (positiveLabel_spec _ n hn).2.2)
  have he := product_perm _ _ ((reduced_labels_perm a n hn hc).map (fun i : Nat => (i : Int)))
  simp only [List.map_map,Function.comp_def] at he
  rw [he,scaled_product] at hp
  have hprod := coprime_product ((reducedResidues n).map (fun i : Nat => (i : Int))) n
    (by omega) (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨i,hi,he⟩
      subst x
      exact ((reduced_mem n i).mp hi).2.2)
  exact cancel_coprime (a^(phi n)) 1 _ n hprod (by simpa [phi] using hp)

theorem euler_shifted_power (a : Int) (n v : Nat) (hn : 0 < n) (ha : gcd a n=1) :
    Congruent (a^(v*phi n+1)) a n := by
  /-
  Theorem: A coprime input raised to one more than a multiple of
  phi(n) returns the original input modulo n.
  Proof: Euler's theorem makes a^phi(n) congruent to one. Its
  v-th power is still one. Multiplication by a gives the stated
  exponent and returns a. This also allows v=0. QED
  -/
  have h := power_multiple_one a n (phi n) v (euler_power a n hn ha)
  rw [Nat.mul_comm (phi n) v] at h
  rw [Int.pow_succ]
  simpa only [Int.one_mul] using modeq_mult _ 1 a a n h (modeq_refl a n (by omega))

theorem positive_inverse_exponents (E n : Nat) (hE : 0 < E) (hn : 0 < n)
    (hc : gcd (E : Int) n=1) :
    ∃ D y : Nat, 0 < D ∧ 0 < y ∧ E*D=1+y*n := by
  /-
  Lemma: A positive integer E coprime to a positive n admits
  positive D and y with ED=1+yn. Proof: Bezout gives E*u+n*v=1.
  Replace u by its nonnegative representative b modulo n and
  choose D=b+2n. Then D is positive and E*D is congruent to one.
  Write E*D-1=n*y. Since E≥1 and D≥2n≥2, the left side is
  positive, so y is positive as well. Thus both required integers
  can be regarded as positive natural numbers. QED
  -/
  rcases bezout (E : Int) n with ⟨u,v,he⟩
  rw [hc] at he
  let b := canonicalLabel u n
  let D := b+2*n
  have hs := canonicalLabel_spec u n hn
  have hDb : Congruent (D : Int) b n := by
    refine ⟨by omega,2,?_⟩
    dsimp [D]
    simp only [Int.natCast_add,Int.natCast_mul]
    omega
  have hDu := modeq_trans _ _ _ n hDb (modeq_symm _ _ n hs.2)
  have hEu : Congruent ((E : Int)*u) 1 n := by
    refine ⟨by omega,-v,?_⟩
    rw [Int.mul_neg]; omega
  have hED := modeq_trans _ _ _ n
    (modeq_mult E E D u n (modeq_refl _ _ (by omega)) hDu) hEu
  rcases hED.2 with ⟨y,hy⟩
  have hD : 2 ≤ D := by dsimp [D]; omega
  have hbound := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ E)
    (by omega : (0 : Int) ≤ D)
  simp only [Int.one_mul] at hbound
  have hypos : 0 < y := by
    by_cases hy0 : 0 < y
    · exact hy0
    · have hneg := Int.mul_nonneg (by omega : (0 : Int) ≤ n) (by omega : 0 ≤ -y)
      rw [Int.mul_neg] at hneg
      omega
  have hycast : (y.toNat : Int)=y := Int.toNat_of_nonneg (by omega)
  refine ⟨D,y.toNat,by omega,by omega,?_⟩
  have heq : ((E*D : Nat) : Int)=((1+y.toNat*n : Nat) : Int) := by
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one,hycast]
    rw [Int.mul_comm y (n : Int)]
    omega
  omega

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

theorem root_exponents_exist (k n : Nat) (hk : 0 < k) (hn : 0 < n)
    (hc : gcd (k : Int) (phi n)=1) :
    ∃ u v : Nat, 0 < u ∧ 0 < v ∧ k*u=phi n*v+1 := by
  /-
  Theorem: A positive exponent k coprime to phi(n) has positive
  integers u,v with k*u=phi(n)*v+1.
  Proof: Phi(n) is positive. The positive Bezout construction
  applied to k and phi(n) supplies the required two exponents.
  It shifts an integer inverse by a sufficiently large multiple
  of phi(n), making both coefficients positive. QED
  -/
  rcases positive_inverse_exponents k (phi n) hk (phi_positive n hn) hc with ⟨u,v,hu,hv,he⟩
  exact ⟨u,v,hu,hv,by simpa only [Nat.add_comm,Nat.mul_comm] using he⟩

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

theorem coprime_root_criterion (b : Int) (n k u v : Nat)
    (hn : 0 < n) (hk : 0 < k) (hb : gcd b n=1) (he : k*u=phi n*v+1) :
    ∀ x : Int, Congruent (x^k) b n ↔ Congruent x (b^u) n := by
  /-
  Theorem: If k*u=phi(n)*v+1 and b is coprime to n, the roots
  of x^k congruent to b are exactly the class b^u.
  Proof: The candidate satisfies (b^u)^k=b^(k*u), which returns
  b by Euler's theorem. Any solution x is coprime to n. Raising
  its congruence to u gives x^(k*u) congruent to b^u, while the
  left side returns x. Conversely, congruent inputs have
  congruent k-th powers, so every representative of b^u works.
  QED
  -/
  have hcandidate : Congruent ((b^u)^k) b n := by
    rw [power_mul,Nat.mul_comm u k,he,Nat.mul_comm (phi n) v]
    exact euler_shifted_power b n v hn hb
  intro x
  constructor
  · intro hx
    have hc := root_is_coprime x b n k hk hb hx
    have hp := modeq_pow (x^k) b n u hx
    rw [power_mul,he,Nat.mul_comm (phi n) v] at hp
    exact modeq_trans x _ _ n (modeq_symm _ _ n (euler_shifted_power x n v hn hc)) hp
  · intro hx
    exact modeq_trans _ _ _ n (modeq_pow x (b^u) n k hx) hcandidate

theorem coprime_roots_unique (b : Int) (n k : Nat) (hn : 0 < n) (hk : 0 < k)
    (hb : gcd b n=1) (hc : gcd (k : Int) (phi n)=1) :
    ∃ u v : Nat, 0 < u ∧ 0 < v ∧ k*u=phi n*v+1 ∧
      ∀ x : Int, Congruent (x^k) b n ↔ Congruent x (b^u) n := by
  /-
  Theorem: A coprime right-hand side has a unique root class
  when k is coprime to phi(n), and an inverse exponent constructs
  that class. Proof: Choose positive u,v by Bezout, then apply
  the root criterion. It gives both existence of b^u and the
  characterization of every solution as congruent to b^u. QED
  -/
  rcases root_exponents_exist k n hk hn hc with ⟨u,v,hu,hv,he⟩
  exact ⟨u,v,hu,hv,he,coprime_root_criterion b n k u v hn hk hb he⟩

def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d=1 ∨ d=p

def primeProduct : List Nat → Nat
  | [] => 1
  | p::ps => p*primeProduct ps

theorem prime_product_positive (ps : List Nat) (hp : ∀ p ∈ ps, Prime p) :
    0 < primeProduct ps := by
  /-
  Lemma: A product of primes is positive, including the empty
  product one. Proof: Induct on the list; each prime is positive
  and the product of two positive integers is positive. QED
  -/
  induction ps with
  | nil => exact (by decide : 0 < 1)
  | cons p ps ih =>
    exact Nat.mul_pos (by have := (hp p (by simp)).1; omega)
      (ih (fun q hq => hp q (by simp [hq])))

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

theorem distinct_primes_coprime (p q : Nat) (hp : Prime p) (hq : Prime q)
    (hne : p ≠ q) : gcd (p : Int) q=1 := by
  /-
  Lemma: Distinct primes are relatively prime. Proof: If q divides
  p, primality of p makes q either one or p. Both are excluded.
  The prime coprimality criterion therefore gives gcd(p,q)=1. QED
  -/
  apply prime_coprime p q hq
  intro hd
  have hdn : q ∣ p := Int.ofNat_dvd.mp hd
  rcases hp.2 q hdn with h | h
  · have := hq.1; omega
  · exact hne h.symm

theorem prime_coprime_remaining_product (p : Nat) (ps : List Nat) (hp : Prime p)
    (hps : ∀ q ∈ ps, Prime q) (hnot : p ∉ ps) : gcd (p : Int) (primeProduct ps)=1 := by
  /-
  Lemma: A prime is coprime to a product of other primes.
  Proof: It is coprime to every different prime. Induction and
  the coprime-product criterion combine these conditions. The
  empty product one has the Bezout identity p*0+1*1=1. QED
  -/
  induction ps with
  | nil => exact gcd_one_combination p 1 ⟨0,1,by simp⟩
  | cons q ps ih =>
    rw [primeProduct,Int.natCast_mul,coprime_product_iff]
    refine ⟨distinct_primes_coprime p q hp (hps q (by simp)) ?_,?_⟩
    · intro he; subst q; exact hnot (by simp)
    · exact ih (fun r hr => hps r (by simp [hr])) (fun h => hnot (by simp [h]))

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

theorem same_members_perm (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup)
    (h : ∀ i, i ∈ xs ↔ i ∈ ys) : xs.Perm ys := by
  /-
  Lemma: Two distinct lists with the same members are rearrangements.
  Proof: Each list is drawn from the other, so the distinct-list
  bound gives both length inequalities. The equal-length selection
  theorem then gives the rearrangement. QED
  -/
  have h₁ := distinct_length_bound xs ys hx (fun i hi => (h i).mp hi)
  have h₂ := distinct_length_bound ys xs hy (fun i hi => (h i).mpr hi)
  exact distinct_subset_perm xs ys hx (fun i hi => (h i).mp hi) (by omega)

def Noncongruent (reps : List Int) (n : Nat) : Prop :=
  reps.Nodup ∧ ∀ a ∈ reps, ∀ b ∈ reps, a ≡ b [MOD (n : Int)] → a=b

def CompleteResidues (reps : List Int) (n : Nat) : Prop :=
  Noncongruent reps n ∧ ∀ a : Int, ∃ r : Int, r ∈ reps ∧ a ≡ r [MOD (n : Int)]

noncomputable def coprimeCount (xs : List Int) (n : Int) : Nat :=
  (xs.filter (fun a => decide (gcd a n=1))).length

theorem complete_coprime_count (xs : List Int) (n : Nat) (hn : 0 < n)
    (hs : CompleteResidues xs n) : coprimeCount xs n=phi n := by
  /-
  Theorem: Every complete residue system modulo n contains exactly
  phi(n) entries coprime to n.
  Proof: Replace each coprime entry by its positive representative
  between one and n. Congruence preserves coprimality, so these
  labels belong to the reduced list. Two equal labels would give
  congruent original entries, hence the same entry. Conversely,
  completeness supplies an entry congruent to any reduced label;
  this entry is coprime, and its positive label is the one requested.
  Thus the two lists have the same entries without repetitions,
  and consequently have the same length. QED
  -/
  let ys := xs.filter (fun a => decide (gcd a (n : Int)=1))
  have hymem : ∀ a ∈ ys, a ∈ xs ∧ gcd a n=1 := by
    intro a ha
    have h := List.mem_filter.mp ha
    exact ⟨h.1,of_decide_eq_true h.2⟩
  have hynd : ys.Nodup := hs.1.1.filter _
  have hnd : (ys.map (fun a => positiveLabel a n)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ hynd
    intro a b ha hb hab he
    have hla := (positiveLabel_spec a n hn).2.2
    have hlb := (positiveLabel_spec b n hn).2.2
    rw [he] at hla
    exact hab (hs.1.2 a (hymem a ha).1 b (hymem b hb).1
      (modeq_trans _ _ _ n hla (modeq_symm _ _ n hlb)))
  have hperm : (ys.map (fun a => positiveLabel a n)).Perm (reducedResidues n) := by
    apply same_members_perm _ _ hnd (reduced_nodup n)
    intro i
    constructor
    · intro hi
      rcases List.mem_map.mp hi with ⟨a,ha,hai⟩
      subst i
      have hl := positiveLabel_spec a n hn
      exact (reduced_mem n _).mpr ⟨hl.1,hl.2.1,
        congruent_coprime a (positiveLabel a n) n (hymem a ha).2 hl.2.2⟩
    · intro hi
      have hi' := (reduced_mem n i).mp hi
      rcases hs.2 (i : Int) with ⟨a,ha,hia⟩
      have hc := congruent_coprime i a n hi'.2.2 hia
      have hl := positiveLabel_spec a n hn
      have he := positive_congruent_equal i (positiveLabel a n) n
        (by omega) (by omega) (by omega) (by omega)
        (modeq_trans _ _ _ n hia hl.2.2)
      exact List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨ha,by simpa using hc⟩,by omega⟩
  have hlen := hperm.length_eq
  simpa only [List.length_map,ys,coprimeCount,phi] using hlen

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

theorem labels_distinct (reps : List Int) (n : Nat) (hn : 0 < n)
    (h : Noncongruent reps n) : (reps.map (fun a => canonicalLabel a n)).Nodup := by
  /-
  Lemma: Replacing noncongruent representatives by their canonical
  labels preserves distinctness. Proof: If two labels were equal,
  the corresponding entries would be congruent. The hypothesis would
  make those entries equal, contrary to their distinctness in the list.
  QED
  -/
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem ?_ h.1
  intro a b ha hb hne he
  exact hne (h.2 a ha b hb ((canonicalLabel_eq_iff a b n hn).mp he))

theorem noncongruent_full_length_complete (reps : List Int) (n : Nat) (hn : 0 < n)
    (h : Noncongruent reps n) (hlen : reps.length=n) : CompleteResidues reps n := by
  /-
  Theorem: Any n pairwise noncongruent integers form a complete
  residue system modulo n.
  Proof: Their canonical labels are n distinct members of 0,...,n-1.
  If a label were missing, adjoining it would give n+1 distinct
  members of a list with only n entries, contradicting the counting
  bound. Thus the canonical label of any integer a occurs. Its
  corresponding representative is congruent to a. This proves coverage;
  noncongruence already gives uniqueness. QED
  -/
  refine ⟨h,?_⟩
  intro a
  let labels := reps.map (fun b => canonicalLabel b n)
  have hnd : labels.Nodup := labels_distinct reps n hn h
  have hsub : ∀ r ∈ labels, r ∈ List.range n := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨b,_,he⟩
    apply List.mem_range.mpr
    have hb := canonicalLabel_spec b n hn
    omega
  have hmem : canonicalLabel a n ∈ labels := by
    apply Classical.byContradiction
    intro hnot
    have hmore : (canonicalLabel a n :: labels).Nodup := List.nodup_cons.mpr ⟨hnot,hnd⟩
    have hmoreSub : ∀ r ∈ canonicalLabel a n :: labels, r ∈ List.range n := by
      intro r hr
      rcases List.mem_cons.mp hr with he | ht
      · subst r
        exact List.mem_range.mpr (canonicalLabel_spec a n hn).1
      · exact hsub r ht
    have hb := distinct_length_bound (canonicalLabel a n :: labels) (List.range n) hmore hmoreSub
    simp only [List.length_cons,List.length_range,labels,List.length_map,hlen] at hb
    omega
  rcases List.mem_map.mp hmem with ⟨b,hb,he⟩
  exact ⟨b,hb,(canonicalLabel_eq_iff a b n hn).mp he.symm⟩

def progression (k m : Int) (n : Nat) : List Int :=
  (List.range n).map (fun j : Nat => k+(j : Int)*m)

theorem progression_nodup_positive (i m : Int) (n : Nat) (hm : 0 < m) :
    (progression i m n).Nodup := by
  /-
  Lemma: A progression with positive step has no repetitions.
  Proof: Equality of two terms cancels the starting value and
  then the nonzero step, leaving equal positions. QED
  -/
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp (R := fun j k : Nat => j ≠ k) ?_ (List.nodup_range n)
  intro j k hjk he
  have he' : (j : Int)*m=(k : Int)*m := by omega
  have heq := Int.eq_of_mul_eq_mul_right (by omega : m ≠ 0) he'
  exact hjk (by omega)

def gridRows (m n : Nat) : List Nat → List Int
  | [] => []
  | i::is => progression i m n ++ gridRows m n is

theorem grid_mem (m n : Nat) (is : List Nat) (a : Int) :
    a ∈ gridRows m n is ↔ ∃ i ∈ is, a ∈ progression i m n := by
  /-
  Lemma: An array entry belongs to one of its listed columns.
  Proof: Unfold the first column and use membership in an
  append, then proceed through the remaining columns. QED
  -/
  induction is with
  | nil => simp [gridRows]
  | cons i is ih =>
    simp only [gridRows,List.mem_append,ih,List.mem_cons]
    constructor
    · intro h
      rcases h with h | ⟨j,hj,ha⟩
      · exact ⟨i,Or.inl rfl,h⟩
      · exact ⟨j,Or.inr hj,ha⟩
    · rintro ⟨j,hj,ha⟩
      rcases hj with hj | hj
      · subst j; exact Or.inl ha
      · exact Or.inr ⟨j,hj,ha⟩

theorem progression_mem (k m a : Int) (n : Nat) :
    a ∈ progression k m n ↔ ∃ j : Nat, j < n ∧ a=k+(j : Int)*m := by
  /-
  Lemma: An entry of a progression has its indicated position j,
  with 0≤j<n. Proof: Unpack the map of the natural-number range.
  The converse inserts that position into the mapped list. QED
  -/
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j,hj,he⟩
    exact ⟨j,List.mem_range.mp hj,he.symm⟩
  · rintro ⟨j,hj,he⟩
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,he.symm⟩

theorem column_congruent (i : Int) (m n : Nat) (hm : 0 < m)
    (a : Int) (ha : a ∈ progression i m n) : Congruent a i m := by
  /-
  Lemma: Every entry in the column with starting value i and
  step m is congruent to i modulo m.
  Proof: At position j its difference from i is j*m, explicitly
  a multiple of m. QED
  -/
  rcases (progression_mem i m a n).mp ha with ⟨j,_,he⟩
  refine ⟨by omega,(j : Int),?_⟩
  rw [he,Int.mul_comm (m : Int) j]
  omega

theorem grid_nodup (m n : Nat) (hm : 0 < m) (is : List Nat)
    (hnd : is.Nodup) (his : ∀ i ∈ is, 0 < i ∧ i ≤ m) :
    (gridRows m n is).Nodup := by
  /-
  Lemma: Distinct columns starting between one and m produce
  distinct entries in the array.
  Proof: Each column has positive step and no repeated entries.
  If entries in two columns were equal, their starting values
  would be congruent modulo m. Both starts lie between one and
  m, so they would be equal, contradicting distinctness of the
  column list. Induction appends all the columns. QED
  -/
  induction is with
  | nil => exact List.Pairwise.nil
  | cons i is ih =>
    have hp := List.pairwise_cons.mp hnd
    have hi := his i (by simp)
    apply List.pairwise_append.mpr
    refine ⟨progression_nodup_positive i m n (by omega),
      ih hp.2 (fun j hj => his j (by simp [hj])),?_⟩
    intro a ha b hb hab
    rcases (grid_mem m n is b).mp hb with ⟨j,hj,hbj⟩
    have hj' := his j (by simp [hj])
    have hai := column_congruent i m n hm a ha
    have hbj' := column_congruent j m n hm b hbj
    rw [hab] at hai
    have hij := modeq_trans i b j m (modeq_symm b i m hai) hbj'
    have he := positive_congruent_equal i j m (by omega) (by omega)
      (by omega) (by omega) hij
    exact hp.1 j hj (by omega)

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

theorem grid_bounds (m n : Nat) (hm : 0 < m) (a : Int)
    (ha : a ∈ gridRows m n (positiveRange m)) : 0 < a ∧ a ≤ (m*n : Nat) := by
  /-
  Lemma: The standard m-wide, n-high array has all its entries
  between one and mn.
  Proof: An entry is i+j*m, where 1≤i≤m and 0≤j<n. It is
  positive, and it is at most (j+1)*m≤n*m=mn. QED
  -/
  rcases (grid_mem m n _ a).mp ha with ⟨i,hi,hai⟩
  have hi' := (positive_range_mem m i).mp hi
  rcases (progression_mem i m a n).mp hai with ⟨j,hj,he⟩
  have hnonneg := Int.mul_nonneg (by omega : (0 : Int) ≤ j) (by omega : (0 : Int) ≤ m)
  have hbound := Int.mul_le_mul_of_nonneg_right (by omega : (j : Int)+1 ≤ n)
    (by omega : (0 : Int) ≤ m)
  rw [Int.add_mul,Int.one_mul,Int.mul_comm (n : Int) m] at hbound
  simp only [Int.natCast_mul]
  omega

theorem grid_length (m n : Nat) (is : List Nat) :
    (gridRows m n is).length=is.length*n := by
  /-
  Lemma: An array with t columns, each of height n, has t*n
  entries. Proof: Each progression has n entries. Appending
  one more column adds n to the total, giving the formula
  by induction on the column list. QED
  -/
  induction is with
  | nil => simp only [gridRows,List.length_nil,Nat.zero_mul]
  | cons i is ih =>
    simp only [gridRows,List.length_append,progression,List.length_map,
      List.length_range,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem grid_complete (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    CompleteResidues (gridRows m n (positiveRange m)) (m*n) := by
  /-
  Lemma: The standard rectangular array is a complete residue
  system modulo mn.
  Proof: Its mn entries are distinct and lie between one and mn.
  Congruent entries in that interval are equal. There are mn
  entries, so the elementary full-length criterion proves
  coverage of all residue classes. QED
  -/
  apply noncongruent_full_length_complete _ (m*n) (Nat.mul_pos hm hn)
  · constructor
    · exact grid_nodup m n hm _ (positive_range_nodup m)
        (fun i hi => (positive_range_mem m i).mp hi)
    · intro a ha b hb hab
      have hba := grid_bounds m n hm a ha
      have hbb := grid_bounds m n hm b hb
      exact positive_congruent_equal a b (m*n : Nat) hba.1 hba.2 hbb.1 hbb.2 hab
  · rw [grid_length]
    simp only [positiveRange,List.length_map,List.length_range]

theorem coprime_count_append (xs ys : List Int) (n : Int) :
    coprimeCount (xs++ys) n=coprimeCount xs n+coprimeCount ys n := by
  /-
  Lemma: Counts add when lists are appended.
  Proof: Filtering an append filters both parts, and the length
  of their append is the sum of their lengths. QED
  -/
  simp only [coprimeCount,List.filter_append,List.length_append]

theorem coprime_count_congr (xs : List Int) (m n : Int)
    (h : ∀ a ∈ xs, gcd a m=1 ↔ gcd a n=1) :
    coprimeCount xs m=coprimeCount xs n := by
  /-
  Lemma: Two coprimality tests with the same answers on a list
  count the same entries. Proof: At the first entry the two
  tests agree. Keep it in both lists or discard it from both,
  then use induction for the remaining entries. QED
  -/
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    by_cases hm : gcd a m=1
    · have hn := ha.mp hm
      simpa [coprimeCount,hm,hn] using congrArg Nat.succ ht
    · have hn : gcd a n ≠ 1 := fun hn => hm (ha.mpr hn)
      simpa [coprimeCount,hm,hn] using ht

theorem column_coprime_iff (i : Int) (m n : Nat) (hm : 0 < m)
    (a : Int) (ha : a ∈ progression i m n) : gcd a m=1 ↔ gcd i m=1 := by
  /-
  Lemma: All entries of a column have the same coprimality
  status with its step m.
  Proof: Each entry is congruent to the starting value. Apply
  preservation of coprimality in each direction. QED
  -/
  have h := column_congruent i m n hm a ha
  exact ⟨fun hc => congruent_coprime a i m hc h,
    fun hc => congruent_coprime i a m hc (modeq_symm a i m h)⟩

theorem progression_noncongruent (k m : Int) (n : Nat) (hn : 0 < n)
    (hc : gcd m n=1) : Noncongruent (progression k m n) n := by
  /-
  Lemma: If the step m is coprime to n, the first n terms of a
  progression are pairwise incongruent modulo n.
  Proof: Congruence of positions i,j cancels the common start k.
  Coprime cancellation then gives i congruent to j. Since both
  positions lie between zero and n-1, they are equal. This also
  proves that no two positions produce the same entry. QED
  -/
  have hindex : ∀ i j : Nat, i<n → j<n →
      Congruent (k+(i : Int)*m) (k+(j : Int)*m) n → i=j := by
    intro i j hi hj hij
    have hmul : Congruent ((i : Int)*m) ((j : Int)*m) n := by
      refine ⟨by omega,?_⟩
      have he : (k+(i : Int)*m)-(k+(j : Int)*m)=(i : Int)*m-(j : Int)*m := by omega
      have hdiv := hij.2
      rw [he] at hdiv
      exact hdiv
    have he := bounded_congruent_equal i j n (by omega) (by omega)
      (by omega) (by omega) (cancel_coprime i j m n hc hmul)
    omega
  constructor
  · apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ (List.nodup_range n)
    intro i j hi hj hij he
    apply hij
    apply hindex i j (List.mem_range.mp hi) (List.mem_range.mp hj)
    rw [he]
    exact ⟨by omega,0,by simp⟩
  · intro a ha b hb hab
    rcases (progression_mem k m a n).mp ha with ⟨i,hi,hai⟩
    rcases (progression_mem k m b n).mp hb with ⟨j,hj,hbj⟩
    rw [hai,hbj] at hab
    have he := hindex i j hi hj hab
    rw [hai,hbj,he]

theorem progression_complete (k m : Int) (n : Nat) (hn : 0 < n)
    (hc : gcd m n=1) : CompleteResidues (progression k m n) n := by
  /-
  Theorem: Any n-term arithmetic progression with step coprime
  to n is a complete residue system modulo n.
  Proof: Its n entries are pairwise incongruent by cancellation.
  A list of n incongruent entries must cover all n possible
  remainders, so it is complete. The starting point and step may
  be arbitrary integers; n is positive. QED
  -/
  apply noncongruent_full_length_complete _ n hn (progression_noncongruent k m n hn hc)
  simp only [progression,List.length_map,List.length_range]

theorem column_product_count (i : Int) (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (hc : gcd (m : Int) n=1) :
    coprimeCount (progression i m n) (m*n : Nat)=if gcd i m=1 then phi n else 0 := by
  /-
  Lemma: For coprime positive m,n, a column contributes phi(n)
  entries coprime to mn if its start is coprime to m, and zero
  otherwise.
  Proof: An entry is coprime to mn exactly when it is coprime
  to both factors. Its condition modulo m is constant throughout
  the column. If that condition fails, nothing qualifies. If it
  holds, only coprimality to n remains. Step m is coprime to n,
  so the column is a complete residue system modulo n and has
  exactly phi(n) such entries. QED
  -/
  by_cases hi : gcd i m=1
  · rw [if_pos hi]
    have he : coprimeCount (progression i m n) (m*n : Nat)=
        coprimeCount (progression i m n) n := by
      apply coprime_count_congr
      intro a ha
      have ham := (column_coprime_iff i m n hm a ha).mpr hi
      rw [Int.natCast_mul,coprime_product_iff]
      exact ⟨fun h => h.2,fun h => ⟨ham,h⟩⟩
    rw [he]
    exact complete_coprime_count _ n hn (progression_complete i m n hn hc)
  · rw [if_neg hi]
    have hnone : ∀ a ∈ progression i m n, gcd a (m*n : Nat) ≠ 1 := by
      intro a ha hab
      rw [Int.natCast_mul,coprime_product_iff] at hab
      exact hi ((column_coprime_iff i m n hm a ha).mp hab.1)
    have hfilter : (progression i m n).filter (fun a => decide (gcd a (m*n : Nat)=1))=[] := by
      apply List.filter_eq_nil.mpr
      intro a ha
      intro hd
      exact hnone a ha (of_decide_eq_true hd)
    simp only [coprimeCount,hfilter,List.length_nil]

theorem grid_product_count (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (hc : gcd (m : Int) n=1) (is : List Nat) :
    coprimeCount (gridRows m n is) (m*n : Nat) =
      phi n * (is.filter (fun i : Nat => decide (gcd (i : Int) m=1))).length := by
  /-
  Lemma: The total number of array entries coprime to mn is
  phi(n) times the number of column starts coprime to m.
  Proof: Each such column contributes phi(n), and the other
  columns contribute zero. Add the column counts by induction.
  QED
  -/
  induction is with
  | nil => simp [gridRows,coprimeCount]
  | cons i is ih =>
    rw [gridRows,coprime_count_append,column_product_count i m n hm hn hc,ih]
    by_cases hi : gcd (i : Int) m=1
    · simp [hi,Nat.mul_add,Nat.add_comm]
    · simp [hi]

theorem phi_multiply (m n : Nat) (hm : 0 < m) (hn : 0 < n)
    (hc : gcd (m : Int) n=1) : phi (m*n)=phi m*phi n := by
  /-
  Theorem: Phi is multiplicative on relatively prime positive
  integers.
  Proof: Arrange 1,...,mn into m columns of height n, with
  entries i,i+m,...,i+(n-1)*m. There are phi(m) columns whose
  starts are coprime to m. Each contributes exactly phi(n)
  entries coprime to mn, because its progression is a complete
  residue system modulo n. The other columns contribute none.
  The array itself is a complete residue system modulo mn, so
  its total count is phi(mn). Hence phi(mn)=phi(m)*phi(n).
  The argument includes m=1 or n=1. QED
  -/
  have h := complete_coprime_count (gridRows m n (positiveRange m)) (m*n)
    (Nat.mul_pos hm hn) (grid_complete m n hm hn)
  rw [grid_product_count m n hm hn hc] at h
  change phi n * phi m=phi (m*n) at h
  rw [← h,Nat.mul_comm]

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

theorem phi_prime (p : Nat) (hp : Prime p) : phi p=p-1 := by
  /-
  Lemma: There are p-1 reduced representatives for a prime p.
  Proof: Every positive integer below p is coprime to p. The
  remaining candidate p is not: a Bezout identity would make p
  divide one. Thus the reduced list has exactly the nonzero
  canonical entries, whose number is p-1. QED
  -/
  have hself : gcd (p : Int) p ≠ 1 := by
    intro hc
    rcases bezout (p : Int) p with ⟨u,v,he⟩
    rw [hc] at he
    have hd : (p : Int) ∣ 1 := ⟨u+v,by rw [Int.mul_add]; omega⟩
    have hb := divisor_le_positive p 1 (by decide) hd
    have := hp.1
    omega
  have hperm : (reducedResidues p).Perm (nonzeroResidues p) := by
    apply same_members_perm _ _ (reduced_nodup p) ((List.nodup_range p).erase 0)
    intro i
    change i ∈ reducedResidues p ↔ i ∈ nonzeroResidues p
    rw [reduced_mem,nonzero_residues_mem]
    constructor
    · rintro ⟨hi,hip,hc⟩
      have hne : i ≠ p := by intro he; subst i; exact hself hc
      exact ⟨hi,by omega⟩
    · rintro ⟨hi,hip⟩
      exact ⟨hi,by omega,small_prime_coprime p i hp hi hip⟩
  have hl := List.length_erase_of_mem (by simp; have := hp.1; omega : 0 ∈ List.range p)
  have he := hperm.length_eq
  simp only [List.length_range] at hl
  change (reducedResidues p).length=p-1
  exact he.trans hl

theorem prime_predecessor_divides_totient (ps : List Nat) (hnd : ps.Nodup)
    (hps : ∀ q ∈ ps, Prime q) (p : Nat) (hp : p ∈ ps) :
    p-1 ∣ phi (primeProduct ps) := by
  /-
  Lemma: If a square-free product contains p, its totient is a
  multiple of p-1. Proof: Separate the first prime q from the
  remaining product. The factors are coprime, so the totient
  splits into phi(q) times the remaining totient. If p=q, the
  first factor is p-1. Otherwise induction supplies the divisor
  in the remaining factor. QED
  -/
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    have hq := hps q (by simp)
    have ht : ∀ r ∈ ps, Prime r := fun r hr => hps r (by simp [hr])
    have hpair := List.nodup_cons.mp hnd
    rw [primeProduct,phi_multiply q (primeProduct ps)
      (by have := hq.1; omega) (prime_product_positive ps ht)
      (prime_coprime_remaining_product q ps hq ht hpair.1)]
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      rw [phi_prime q hq]
      exact ⟨phi (primeProduct ps),rfl⟩
    · rcases ih hpair.2 ht hp with ⟨t,he⟩
      exact ⟨phi q*t,by rw [he]; simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]⟩

theorem product_divides (n m z : Int)
    (hcop : ∃ u v : Int, n*u+m*v=1) :
    (n ∣ z ∧ m ∣ z) ↔ n*m ∣ z := by
  /-
  Lemma: If n and m have a linear combination equal to one, their
  product divides z exactly when each of them divides z.
  Proof: Write z=n*i=m*j and n*u+m*v=1. Multiplication gives
  z=z*(n*u+m*v)=n*m*(j*u+i*v). This is a product-divisibility
  witness. Conversely, z=n*m*k exhibits factors n and m separately.
  QED
  -/
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    rcases hcop with ⟨u,v,he⟩
    refine ⟨j*u+i*v,?_⟩
    have h₁ : z*(n*u)=(n*m)*(j*u) := by
      rw [hj]
      simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    have h₂ : z*(m*v)=(n*m)*(i*v) := by
      rw [hi]
      simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    calc
      z = z*1 := by rw [Int.mul_one]
      _ = z*(n*u+m*v) := congrArg (fun t => z*t) he.symm
      _ = (n*m)*(j*u+i*v) := by rw [Int.mul_add,h₁,h₂,Int.mul_add]
  · rintro ⟨k,hk⟩
    constructor
    · exact ⟨m*k,by rw [hk,Int.mul_assoc]⟩
    · refine ⟨n*k,?_⟩
      rw [hk]
      simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]

theorem combine_coprime_moduli (x a : Int) (n m : Nat)
    (hc : gcd (n : Int) m=1) (hn : Congruent x a n) (hm : Congruent x a m) :
    Congruent x a ((n : Int)*m) := by
  /-
  Theorem: Congruence to the same integer modulo two relatively
  prime positive moduli implies congruence modulo their product.
  Proof: Both moduli divide x-a. Their Bezout identity equals one,
  so the product-divisibility lemma shows that their product
  divides x-a. The product is positive, as required. QED
  -/
  have hb := bezout (n : Int) m
  rw [hc] at hb
  exact ⟨Int.mul_pos hn.1 hm.1,(product_divides n m (x-a) hb).mp ⟨hn.2,hm.2⟩⟩

theorem combine_prime_moduli (ps : List Nat) (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, Prime p) (a b : Int)
    (h : ∀ p ∈ ps, Congruent a b p) : Congruent a b (primeProduct ps) := by
  /-
  Lemma: Congruence modulo each of a list of distinct primes
  implies congruence modulo their product.
  Proof: Induct on the list, combining the first prime with
  the remaining product. They are coprime, so divisibility of
  the difference by both implies divisibility by their product.
  For the empty list every difference is a multiple of one. QED
  -/
  induction ps with
  | nil => exact ⟨by decide,a-b,by simp [primeProduct]⟩
  | cons p ps ih =>
    have hp := hps p (by simp)
    have ht : ∀ q ∈ ps, Prime q := fun q hq => hps q (by simp [hq])
    have hpair := List.nodup_cons.mp hnd
    exact combine_coprime_moduli a b p (primeProduct ps)
      (prime_coprime_remaining_product p ps hp ht hpair.1)
      (h p (by simp)) (ih hpair.2 ht (fun q hq => h q (by simp [hq])))

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

theorem prime_shifted_power (W : Int) (p k : Nat) (hp : Prime p) :
    Congruent (W^(1+k*(p-1))) W p := by
  /-
  Lemma: Exponents one greater than a multiple of p-1 return W
  modulo a prime p. Proof: If p divides W, the positive power
  W^(k*(p-1))*W and W are both zero modulo p. Otherwise W is
  coprime to p. Fermat's theorem, raised to power k, makes the
  first factor one modulo p. Multiplying by W proves the claim.
  This also includes k=0 and W=0. QED
  -/
  have hn : 0 < (p : Int) := by have := hp.1; omega
  have he : W^(1+k*(p-1))=W^(k*(p-1))*W := by
    rw [Nat.add_comm,Int.pow_succ]
  rw [he]
  by_cases hd : (p : Int) ∣ W
  · have hz : Congruent W 0 p := ⟨hn,by simpa using hd⟩
    have hm := modeq_mult _ (W^(k*(p-1))) W 0 p (modeq_refl _ _ hn) hz
    simp only [Int.mul_zero] at hm
    exact modeq_trans _ _ _ p hm (modeq_symm _ _ p hz)
  · have hm := power_multiple_one W p (p-1) k (fermat_coprime W p hp (prime_coprime W p hp hd))
    rw [Nat.mul_comm (p-1) k] at hm
    simpa only [Int.one_mul] using modeq_mult _ 1 W W p hm (modeq_refl _ _ hn)

theorem squarefree_shifted_power (a : Int) (ps : List Nat) (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, Prime p) (v : Nat) :
    Congruent (a^(v*phi (primeProduct ps)+1)) a (primeProduct ps) := by
  /-
  Theorem: For a product of distinct primes, raising any integer
  to one more than a multiple of the totient returns it modulo
  the product. No coprimality of the input is needed.
  Proof: For each prime p in the product, write phi(n)=(p-1)*t.
  The exponent is then 1+(v*t)*(p-1), which returns a modulo p:
  Fermat handles nonmultiples of p, and multiples remain zero.
  Combine the congruences over the distinct prime factors. QED
  -/
  apply combine_prime_moduli ps hnd hps
  intro p hp
  rcases prime_predecessor_divides_totient ps hnd hps p hp with ⟨t,ht⟩
  have he : v*phi (primeProduct ps)+1=1+(v*t)*(p-1) := by
    rw [ht]
    simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm,Nat.add_comm]
  rw [he]
  exact prime_shifted_power a p (v*t) (hps p hp)

theorem squarefree_root_criterion (b : Int) (ps : List Nat) (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, Prime p) (k u v : Nat) (he : k*u=phi (primeProduct ps)*v+1) :
    ∀ x : Int, Congruent (x^k) b (primeProduct ps) ↔ Congruent x (b^u) (primeProduct ps) := by
  /-
  Theorem: For a square-free modulus n and k*u=phi(n)*v+1,
  the roots of b form exactly the class b^u, for every integer b.
  Proof: The square-free power identity makes (b^u)^k congruent
  to b. Raising any root congruence to u makes its left side
  return x, so every root is congruent to b^u. Conversely,
  congruent representatives of b^u have the same k-th power.
  QED
  -/
  have hb : Congruent ((b^u)^k) b (primeProduct ps) := by
    rw [power_mul,Nat.mul_comm u k,he,Nat.mul_comm (phi (primeProduct ps)) v]
    exact squarefree_shifted_power b ps hnd hps v
  intro x
  constructor
  · intro hx
    have h := modeq_pow (x^k) b (primeProduct ps) u hx
    rw [power_mul,he,Nat.mul_comm (phi (primeProduct ps)) v] at h
    exact modeq_trans _ _ _ (primeProduct ps)
      (modeq_symm _ _ _ (squarefree_shifted_power x ps hnd hps v)) h
  · intro hx
    exact modeq_trans _ _ _ (primeProduct ps) (modeq_pow x (b^u) _ k hx) hb

theorem squarefree_roots_unique (b : Int) (ps : List Nat) (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, Prime p) (k : Nat) (hk : 0 < k)
    (hc : gcd (k : Int) (phi (primeProduct ps))=1) :
    ∃ u v : Nat, 0 < u ∧ 0 < v ∧ k*u=phi (primeProduct ps)*v+1 ∧
      ∀ x : Int, Congruent (x^k) b (primeProduct ps) ↔ Congruent x (b^u) (primeProduct ps) := by
  /-
  Theorem: For a product of distinct primes, an exponent coprime
  to the totient gives a unique root class for every right-hand
  side. Proof: Choose positive inverse exponents by Bezout and
  apply the square-free root criterion. A list of distinct prime
  factors represents the modulus without assuming a library
  square-free theorem. The empty list also covers modulus one.
  QED
  -/
  rcases root_exponents_exist k (primeProduct ps) hk (prime_product_positive ps hps) hc with
    ⟨u,v,hu,hv,he⟩
  exact ⟨u,v,hu,hv,he,squarefree_root_criterion b ps hnd hps k u v he⟩

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

theorem prime_divides_power (p : Nat) (a : Int) (hp : Prime p) (k : Nat)
    (h : (p : Int) ∣ a^k) : (p : Int) ∣ a := by
  /-
  Lemma: If a prime divides a power, it divides the base.
  Proof: For exponent zero the hypothesis would make a prime
  divide one, which is impossible. At a successor exponent,
  prime divisibility of the product a^k*a gives divisibility of
  a directly or of a^k, where induction applies. QED
  -/
  induction k with
  | zero =>
    simp only [Int.pow_zero] at h
    have hb := divisor_le_positive p 1 (by decide) h
    have := hp.1
    omega
  | succ k ih =>
    rw [Int.pow_succ] at h
    rcases prime_product_divides p (a^k) a hp h with h | h
    · exact ih h
    · exact h

def rootResidues (n k : Nat) (b : Int) : List Nat :=
  (List.range n).filter (fun x : Nat => decide (0 < (n : Int) ∧ (n : Int) ∣ (x : Int)^k-b))

theorem root_residues_mem (n k x : Nat) (b : Int) :
    x ∈ rootResidues n k b ↔ x<n ∧ Congruent ((x : Int)^k) b n := by
  /-
  Lemma: The root list contains exactly the canonical solutions.
  Proof: The range supplies 0≤x<n, and the filter keeps precisely
  the entries whose k-th powers are congruent to b. QED
  -/
  simp only [rootResidues,List.mem_filter,List.mem_range,decide_eq_true_eq,Congruent]

theorem root_residues_nodup (n k : Nat) (b : Int) : (rootResidues n k b).Nodup := by
  /-
  Lemma: The canonical root list has no repetitions.
  Proof: Filtering the range removes entries and never duplicates
  them. Thus its length counts solution classes, not occurrences.
  QED
  -/
  exact (List.nodup_range n).filter _

theorem zero_root_count (p k : Nat) (b : Int) (hp : Prime p) (hk : 0 < k)
    (hb : (p : Int) ∣ b) : (rootResidues p k b).length=1 := by
  /-
  Theorem: If p divides b and k is positive, there is exactly one
  root class of x^k congruent to b modulo p: the zero class.
  Proof: A root has its k-th power divisible by p, so its base
  is divisible by p. In the canonical range this forces x=0.
  Conversely zero is a root because k is positive and b is zero
  modulo p. The root list is therefore a permutation of [0].
  This is the separately proved zero-residue case of the approved
  correction to the root-count statement. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hb0 : Congruent b 0 p := ⟨by omega,by simpa only [Int.sub_zero] using hb⟩
  have hperm : (rootResidues p k b).Perm [0] := by
    apply same_members_perm _ _ (root_residues_nodup p k b) (by simp)
    intro x
    simp only [List.mem_singleton]
    constructor
    · intro hx
      have hs := (root_residues_mem p k x b).mp hx
      have hz := modeq_trans _ _ _ p hs.2 hb0
      have hd := prime_divides_power p x hp k (by simpa only [Int.sub_zero] using hz.2)
      have he := bounded_congruent_equal x 0 p (by omega) (by omega) (by omega) (by omega)
        ⟨by omega,by simpa only [Int.sub_zero] using hd⟩
      omega
    · intro he
      subst x
      apply (root_residues_mem p k 0 b).mpr
      refine ⟨hn,?_⟩
      have he : k=(k-1)+1 := by omega
      rw [he,Int.natCast_zero,Int.pow_succ,Int.mul_zero]
      exact modeq_symm _ _ p hb0
  exact hperm.length_eq

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

theorem powers_congruent_ordered (a : Int) (n i j : Nat) (hn : 0 < n)
    (ha : gcd a n=1) (hij : i ≤ j) :
    Congruent (a^j) (a^i) n ↔ Congruent (j : Int) i (order a n) := by
  /-
  Lemma: For i≤j, equality of the two power classes is equivalent
  to congruence of the exponents modulo the order.
  Proof: Factor a^j=a^(j-i)*a^i. Coprime cancellation makes the
  power congruence equivalent to a^(j-i) congruent to one. This
  is equivalent to the order dividing j-i. Conversely, that
  divisibility returns the first factor to one, and multiplication
  by a^i restores the original power congruence. QED
  -/
  have hd := (order_spec a n hn ha).1
  have hsplit : a^j=a^(j-i)*a^i := by
    rw [← power_add]
    congr 1
    omega
  constructor
  · intro h
    rw [hsplit] at h
    have hc : Congruent (a^(j-i)*a^i) (1*a^i) n := by simpa only [Int.one_mul] using h
    have hret := cancel_coprime (a^(j-i)) 1 (a^i) n (coprime_power a n (by omega) ha i) hc
    have hdiv := Int.ofNat_dvd.mpr ((order_dvd_iff a n hn ha (j-i)).mp hret)
    refine ⟨by omega,?_⟩
    simpa only [Int.ofNat_sub hij] using hdiv
  · intro h
    have hdiv : order a n ∣ j-i := Int.ofNat_dvd.mp (by
      simpa only [Int.ofNat_sub hij] using h.2)
    have hret := (order_dvd_iff a n hn ha (j-i)).mpr hdiv
    rw [hsplit]
    simpa only [Int.one_mul] using modeq_mult _ 1 (a^i) (a^i) n hret (modeq_refl _ n (by omega))

theorem powers_congruent_iff (a : Int) (n i j : Nat) (hn : 0 < n) (ha : gcd a n=1) :
    Congruent (a^i) (a^j) n ↔ Congruent (i : Int) j (order a n) := by
  /-
  Lemma: Two powers of a coprime integer are congruent exactly
  when their exponents are congruent modulo its order.
  Proof: If j≤i, apply the ordered-exponent argument directly.
  Otherwise reverse both congruences, apply that argument, and
  reverse them again. QED
  -/
  by_cases hji : j ≤ i
  · exact powers_congruent_ordered a n j i hn ha hji
  · have h := powers_congruent_ordered a n i j hn ha (by omega)
    exact ⟨fun hx => modeq_symm _ _ _ (h.mp (modeq_symm _ _ n hx)),
      fun hx => modeq_symm _ _ n (h.mpr (modeq_symm _ _ _ hx))⟩

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

def PrimitiveRoot (a : Int) (p : Nat) : Prop := gcd a p=1 ∧ order a p=p-1

theorem primitive_index (a x : Int) (p : Nat) (hp : Prime p) (ha : PrimitiveRoot a p)
    (hx : gcd x p=1) : ∃ e : Nat, e<p-1 ∧ Congruent x (a^(e+1)) p := by
  /-
  Lemma: Every nonzero residue is represented by a primitive
  root power with exponent e+1 for 0≤e<p-1.
  Proof: Fermat makes x^(p-1) congruent to one. A primitive
  root has order p-1, so its full power cycle exhausts these
  roots. Write the supplied exponent i as (i-1)+1. QED
  -/
  have hret := fermat_coprime x p hp hx
  rw [← ha.2] at hret
  rcases power_root_in_cycle a x p hp ha.1 hret with ⟨i,hi,hib,hxi⟩
  rw [ha.2] at hib
  exact ⟨i-1,by omega,by simpa only [Nat.sub_add_cancel hi] using hxi⟩

theorem primitive_power_root_iff (a b : Int) (p k e j : Nat)
    (hp : Prime p) (ha : PrimitiveRoot a p) (hb : Congruent b (a^j) p) :
    Congruent ((a^(e+1))^k) b p ↔
      Congruent ((k : Int)*e) ((j : Int)-k) (p-1 : Nat) := by
  /-
  Lemma: Writing a root as a^(e+1) changes its power congruence
  into the linear congruence k*e congruent to j-k modulo p-1,
  when b is congruent to a^j and a is primitive.
  Proof: The k-th power is a^((e+1)*k). Equality of power classes
  is equivalent to equality of exponents modulo p-1. Subtracting
  the exponents gives k*e-(j-k), exactly the linear difference.
  The shift by one lets the canonical exponents start at zero.
  QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hpow := powers_congruent_iff a p ((e+1)*k) j hn ha.1
  rw [ha.2] at hpow
  have hdiff : (((e+1)*k : Nat) : Int)-(j : Int)=(k : Int)*e-((j : Int)-k) := by
    simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_one,Int.add_mul,Int.one_mul]
    rw [Int.mul_comm (e : Int) k]
    omega
  constructor
  · intro h
    rw [power_mul] at h
    have hexp := hpow.mp (modeq_trans _ _ _ p h hb)
    exact ⟨hexp.1,by rw [← hdiff]; exact hexp.2⟩
  · intro h
    have hexp : Congruent (((e+1)*k : Nat) : Int) j (p-1 : Nat) :=
      ⟨h.1,by rw [hdiff]; exact h.2⟩
    rw [power_mul]
    exact modeq_trans _ _ _ p (hpow.mpr hexp) (modeq_symm _ _ p hb)

theorem primitive_labels_injective (a : Int) (p i j : Nat) (hp : Prime p)
    (ha : PrimitiveRoot a p) (hi : i<p-1) (hj : j<p-1)
    (he : canonicalLabel (a^(i+1)) p=canonicalLabel (a^(j+1)) p) : i=j := by
  /-
  Lemma: Different positions in a primitive power cycle have
  different canonical labels.
  Proof: Equal labels give congruent powers, hence congruent
  exponents modulo p-1. Those exponents lie between one and
  p-1, where congruence implies equality. Subtract one. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hc := (canonicalLabel_eq_iff _ _ p hn).mp he
  have he' := (powers_congruent_iff a p (i+1) (j+1) hn ha.1).mp hc
  rw [ha.2] at he'
  have h := positive_congruent_equal (i+1 : Nat) (j+1 : Nat) (p-1 : Nat)
    (by omega) (by omega) (by omega) (by omega) he'
  omega

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

end NumberTheory.ModularRoots
