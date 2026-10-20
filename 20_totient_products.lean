import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.TotientProducts

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

noncomputable def phi (n : Nat) : Nat := (reducedResidues n).length

theorem phi_one : phi 1=1 := by
  /-
  Lemma: The count at modulus one is one. Proof: The only positive
  representative at most one is one itself, and its gcd with one
  is one. Thus the reduced list has exactly this one member. QED
  -/
  have hp : (reducedResidues 1).Perm [1] := by
    apply same_members_perm _ _ (reduced_nodup 1) (by simp)
    intro i
    rw [reduced_mem]
    simp only [List.mem_singleton]
    constructor
    · intro h; omega
    · intro h
      subst i
      exact ⟨by decide,by decide,gcd_one_combination 1 1 ⟨1,0,by decide⟩⟩
  exact hp.length_eq

theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The gcd of two integers is an integer linear combination.
  Proof: These are the coefficients constructed by the Euclidean
  procedure and back-substitution above. The construction also covers
  the harmless extra case a = b = 0. QED
  -/
  exact (gcd_data a b).2.2.2

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

end NumberTheory.TotientProducts
