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

end NumberTheory.ModularRoots
