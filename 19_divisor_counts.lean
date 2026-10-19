import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.DivisorCounts

def positiveRange (n : Nat) : List Nat := (List.range n).map (fun i => i+1)

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

def divisors (n : Nat) : List Nat := (positiveRange n).filter (fun d => decide (d ∣ n))

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

theorem divisors_nodup (n : Nat) : (divisors n).Nodup := by
  /-
  Lemma: Each divisor is listed only once.
  Proof: Filtering a list without repetitions cannot introduce one.
  QED
  -/
  exact (positive_range_nodup n).filter _

theorem divisor_factor (n d : Nat) (hn : 0 < n) (hd : d ∣ n) :
    0 < n/d ∧ (n/d)*d=n := by
  /-
  Lemma: For a divisor d of positive n, the complementary factor
  n/d is positive and its product with d is n. Proof: Exact integer
  division gives the product identity. A zero quotient would force
  n=0, contrary to its positivity. QED
  -/
  have he := Nat.div_mul_cancel hd
  refine ⟨?_,he⟩
  by_cases hz : n/d=0
  · rw [hz,Nat.zero_mul] at he; omega
  · exact Nat.pos_of_ne_zero hz

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

theorem gcd_eq_of_combination (a b d : Int) (hd : 0 < d)
    (ha : d ∣ a) (hb : d ∣ b) (hxy : ∃ x y : Int, a * x + b * y = d) :
    gcd a b = d := by
  /-
  Theorem: A positive common divisor that is a linear combination of
  the inputs is their gcd. Proof: The inputs cannot both vanish,
  because the combination is positive. Thus d is at most their gcd.
  Conversely, the gcd divides the combination d, so is at most d.
  These two inequalities prove equality. QED
  -/
  rcases hxy with ⟨x, y, heq⟩
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_cases ha₀ : a = 0
    · right
      intro hb₀
      rw [ha₀, hb₀, Int.zero_mul, Int.zero_mul, Int.add_zero] at heq
      omega
    · exact Or.inl ha₀
  have hle := gcd_greatest a b hne d ha hb
  have hdiv := dvd_linear (gcd a b) a b x y (gcd_data a b).2.1 (gcd_data a b).2.2.1
  rw [heq] at hdiv
  have hge := divisor_le_positive (gcd a b) d hd hdiv
  omega

theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The gcd of two integers is an integer linear combination.
  Proof: These are the coefficients constructed by the Euclidean
  procedure and back-substitution above. The construction also covers
  the harmless extra case a = b = 0. QED
  -/
  exact (gcd_data a b).2.2.2

theorem gcd_scale (a b : Int) (k : Nat) (hk : 0 < k) (hne : a ≠ 0 ∨ b ≠ 0) :
    gcd ((k : Int) * a) ((k : Int) * b) = (k : Int) * gcd a b := by
  /-
  Theorem: Multiplying both inputs by a positive natural number k
  multiplies the gcd by k. Proof: Write g=gcd(a,b). The number k*g
  is positive and divides both k*a and k*b. If a*x+b*y=g, then

    (k*a)*x + (k*b)*y = k*g.

  The preceding characterization identifies k*g as the new gcd. QED
  -/
  have hg := gcd_data a b
  apply gcd_eq_of_combination ((k : Int) * a) ((k : Int) * b) ((k : Int) * gcd a b)
  · exact Int.mul_pos (by omega) (gcd_positive a b hne)
  · rcases hg.2.1 with ⟨u, hu⟩
    exists u
    exact (congrArg (fun t : Int => (k : Int) * t) hu).trans (Int.mul_assoc _ _ _).symm
  · rcases hg.2.2.1 with ⟨v, hv⟩
    exists v
    exact (congrArg (fun t : Int => (k : Int) * t) hv).trans (Int.mul_assoc _ _ _).symm
  · rcases bezout a b with ⟨x, y, hxy⟩
    exists x, y
    rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_add, hxy]

/-
For positive inputs, a least common multiple is a positive integer
that both inputs divide and that is no larger than any other positive
common multiple. The expression below will be proved to have exactly
these properties; it does not use a library least-common-multiple theorem.
-/

theorem expanded_fraction_gcd (n d i : Nat) (hn : 0 < n)
    (hd : 0 < d) (hdn : d ∣ n) (hi : gcd (i : Int) d=1) :
    gcd (((n/d)*i : Nat) : Int) n=(n/d : Nat) := by
  /-
  Lemma: Expanding a reduced fraction i/d to denominator n makes
  the gcd of its numerator and n exactly n/d.
  Proof: Put q=n/d, so n=q*d and q>0. Scaling both coprime inputs
  i,d multiplies their gcd one by q. QED
  -/
  have hq := divisor_factor n d hn hdn
  have he := gcd_scale (i : Int) d (n/d) hq.1 (Or.inr (by omega))
  rw [hi,Int.mul_one] at he
  simpa only [← Int.natCast_mul,hq.2] using he

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

theorem reduced_fraction_expansion (n k : Nat) (hn : 0 < n)
    (hk : 0 < k) (hkn : k ≤ n) :
    ∃ d i : Nat, 0 < d ∧ d ∣ n ∧ i ∈ reducedResidues d ∧ k=(n/d)*i := by
  /-
  Lemma: Every fraction k/n with 1≤k≤n is obtained by expanding
  a reduced fraction i/d, where d divides n and 1≤i≤d.
  Proof: Let g=gcd(k,n), which is positive, and write k=g*i and
  n=g*d. Positivity and k≤n give 1≤i≤d. Scaling the gcd shows
  g*gcd(i,d)=g; cancellation gives gcd(i,d)=1. Finally n/d=g,
  so expansion recovers exactly k. QED
  -/
  let g := (gcd (k : Int) n).toNat
  have hgdata := gcd_data (k : Int) n
  have hgcast : (g : Int)=gcd (k : Int) n := Int.toNat_of_nonneg hgdata.1
  have hgpositive := gcd_positive (k : Int) n (Or.inr (by omega))
  have hgp : 0 < g := by omega
  have hgk : g ∣ k := Int.ofNat_dvd.mp (by rw [hgcast]; exact hgdata.2.1)
  have hgn : g ∣ n := Int.ofNat_dvd.mp (by rw [hgcast]; exact hgdata.2.2.1)
  rcases hgk with ⟨i,hki⟩
  rcases hgn with ⟨d,hnd⟩
  have hd : 0 < d := by
    by_cases hz : d=0
    · rw [hz,Nat.mul_zero] at hnd; omega
    · omega
  have hi : 0 < i := by
    by_cases hz : i=0
    · rw [hz,Nat.mul_zero] at hki; omega
    · omega
  have hid : i ≤ d := by
    by_cases h : i ≤ d
    · exact h
    · have := Nat.mul_lt_mul_of_pos_left (by omega : d<i) hgp
      omega
  have hscale := gcd_scale (i : Int) d g hgp (Or.inr (by omega))
  have hcop : gcd (i : Int) d=1 := by
    apply Int.eq_of_mul_eq_mul_left (a := (g : Int)) (by omega)
    rw [← hscale,← Int.natCast_mul,← Int.natCast_mul,← hki,← hnd,← hgcast,Int.mul_one]
  have hquot : n/d=g := by rw [hnd]; exact Nat.mul_div_cancel g hd
  refine ⟨d,i,hd,⟨g,by rw [hnd,Nat.mul_comm]⟩,(reduced_mem d i).mpr ⟨hi,hid,hcop⟩,?_⟩
  rw [hquot]; exact hki

noncomputable def expandedFractions (n : Nat) : List Nat → List Nat
  | [] => []
  | d::ds => ((reducedResidues d).map (fun i => (n/d)*i)) ++ expandedFractions n ds

theorem expanded_fractions_mem (n k : Nat) (ds : List Nat) :
    k ∈ expandedFractions n ds ↔
      ∃ d ∈ ds, ∃ i ∈ reducedResidues d, k=(n/d)*i := by
  /-
  Lemma: The expanded list consists of the numerators obtained by
  expanding each reduced fraction with a listed denominator.
  Proof: Induct on the denominator list. Its first row consists
  exactly of the scaled reduced numerators; append adds the rows
  belonging to the remaining denominators. QED
  -/
  induction ds with
  | nil => simp [expandedFractions]
  | cons d ds ih =>
    simp only [expandedFractions,List.mem_append,List.mem_map,ih,List.mem_cons]
    constructor
    · intro h
      rcases h with h | ⟨e,he,i,hi,hk⟩
      · rcases h with ⟨i,hi,hk⟩; exact ⟨d,Or.inl rfl,i,hi,hk.symm⟩
      · exact ⟨e,Or.inr he,i,hi,hk⟩
    · rintro ⟨e,he,i,hi,hk⟩
      rcases he with he | he
      · subst e; exact Or.inl ⟨i,hi,hk.symm⟩
      · exact Or.inr ⟨e,he,i,hi,hk⟩

theorem fraction_denominator_unique (n d e i j : Nat) (hn : 0 < n)
    (hd : 0 < d) (hdn : d ∣ n) (he : 0 < e) (hen : e ∣ n)
    (hi : gcd (i : Int) d=1) (hj : gcd (j : Int) e=1)
    (h : (n/d)*i=(n/e)*j) : d=e := by
  /-
  Lemma: Two reduced fractions that expand to the same numerator
  over n have the same denominator. Proof: The expanded numerator
  has gcd n/d with n and also gcd n/e with n. Thus these positive
  complementary factors are equal. Cancel that common factor in
  (n/d)*d=n=(n/e)*e to obtain d=e. QED
  -/
  have hg := expanded_fraction_gcd n d i hn hd hdn hi
  have hg' := expanded_fraction_gcd n e j hn he hen hj
  rw [h,hg'] at hg
  have hq : n/d=n/e := by omega
  have hf := divisor_factor n d hn hdn
  have hf' := divisor_factor n e hn hen
  apply Nat.eq_of_mul_eq_mul_left hf.1
  rw [hf.2,hq,hf'.2]

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

theorem expanded_fractions_nodup (n : Nat) (hn : 0 < n) (ds : List Nat)
    (hds : ds.Nodup) (hdiv : ∀ d ∈ ds, 0 < d ∧ d ∣ n) :
    (expandedFractions n ds).Nodup := by
  /-
  Lemma: The expanded reduced fractions have no repeated numerators
  when the denominators are distinct divisors of n.
  Proof: Within one row, multiplication by the positive factor n/d
  is injective. Across rows, equality of numerators would imply
  equality of their reduced denominators, already excluded. Apply
  this observation successively to the rows. QED
  -/
  induction ds with
  | nil => exact List.Pairwise.nil
  | cons d ds ih =>
    have hd := hdiv d (by simp)
    have hp := List.pairwise_cons.mp hds
    apply List.pairwise_append.mpr
    refine ⟨?_,ih hp.2 (fun e he => hdiv e (by simp [he])),?_⟩
    · apply List.pairwise_map.mpr
      apply List.Pairwise.imp (R := fun i j : Nat => i ≠ j) ?_ (reduced_nodup d)
      intro i j hij heq
      exact hij (Nat.eq_of_mul_eq_mul_left (divisor_factor n d hn hd.2).1 heq)
    · intro a ha b hb hab
      rcases List.mem_map.mp ha with ⟨i,hi,hia⟩
      rcases (expanded_fractions_mem n b ds).mp hb with ⟨e,he,j,hj,hbj⟩
      have hed := hdiv e (by simp [he])
      have hde := fraction_denominator_unique n d e i j hn hd.1 hd.2 hed.1 hed.2
        ((reduced_mem d i).mp hi).2.2 ((reduced_mem e j).mp hj).2.2 (by omega)
      exact hp.1 e he hde

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

theorem reduced_fraction_correspondence (n : Nat) (hn : 0 < n) :
    (expandedFractions n (divisors n)).Perm (positiveRange n) := by
  /-
  Theorem: Reducing 1/n,...,n/n gives a one-to-one correspondence
  with the reduced fractions i/d for positive divisors d of n.
  Proof: Reduction supplies every numerator in the original range.
  Conversely expansion of 1≤i≤d gives 1≤(n/d)*i≤n. Distinct
  reduced fractions have distinct expansions, as just proved.
  Thus the two lists contain the same entries without repetitions.
  The fractions are represented by integer numerator-denominator
  pairs, so no rational-number machinery is required. QED
  -/
  apply same_members_perm _ _
    (expanded_fractions_nodup n hn _ (divisors_nodup n)
      (fun d hd => (divisors_mem n d hn).mp hd)) (positive_range_nodup n)
  intro k
  constructor
  · intro hk
    rcases (expanded_fractions_mem n k _).mp hk with ⟨d,hd,i,hi,hk⟩
    have hd' := (divisors_mem n d hn).mp hd
    have hi' := (reduced_mem d i).mp hi
    have hq := divisor_factor n d hn hd'.2
    apply (positive_range_mem n k).mpr
    constructor
    · rw [hk]; exact Nat.mul_pos hq.1 hi'.1
    · have := Nat.mul_le_mul_left (n/d) hi'.2.1
      omega
  · intro hk
    have hk' := (positive_range_mem n k).mp hk
    rcases reduced_fraction_expansion n k hn hk'.1 hk'.2 with ⟨d,i,hd,hdn,hi,hki⟩
    exact (expanded_fractions_mem n k _).mpr ⟨d,(divisors_mem n d hn).mpr ⟨hd,hdn⟩,i,hi,hki⟩

def sumOn : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | d::ds, f => f d + sumOn ds f

noncomputable def phi (n : Nat) : Nat := (reducedResidues n).length

theorem expanded_fractions_length (n : Nat) (ds : List Nat) :
    (expandedFractions n ds).length=sumOn ds phi := by
  /-
  Lemma: The number of expanded fractions is the sum of phi(d)
  over the listed denominators. Proof: A row has one entry for
  each of its phi(d) reduced numerators. Appending a row adds
  its length; induction sums all rows. QED
  -/
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [expandedFractions,List.length_append,List.length_map,ih,sumOn,phi]

noncomputable def divisorSum (n : Nat) : Nat := sumOn (divisors n) phi

theorem totient_divisor_sum (n : Nat) (hn : 0 < n) : divisorSum n=n := by
  /-
  Theorem: Adding phi(d) over the positive divisors of n gives n.
  Proof: Group the fractions 1/n,...,n/n by their denominators
  after reduction. The preceding correspondence places exactly
  phi(d) of them in the row for d, and counts each fraction once.
  The original list has n entries, giving the identity. This is
  the elementary reduced-fraction proof of the divisor-sum formula.
  QED
  -/
  have h := (reduced_fraction_correspondence n hn).length_eq
  rw [expanded_fractions_length] at h
  simpa only [divisorSum,positiveRange,List.length_map,List.length_range] using h

def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d=1 ∨ d=p

theorem prime_divisor_sum (p : Nat) (hp : Prime p) : divisorSum p=p := by
  /-
  Lemma: The totient sum over divisors of a prime p is p.
  Proof: The fraction-counting identity applies to positive p.
  This includes the prime case of the divisor-sum formula. QED
  -/
  exact totient_divisor_sum p (by have := hp.1; omega)

theorem prime_power_divisor_sum (p k : Nat) (hp : Prime p) :
    divisorSum (p^k)=p^k := by
  /-
  Lemma: The totient sum over divisors of p^k equals p^k.
  Proof: A prime is positive, so every power is positive, including
  p^0=1. Apply the reduced-fraction count at this denominator. QED
  -/
  apply totient_divisor_sum
  exact Nat.pow_pos (by have := hp.1; omega)

theorem two_prime_divisor_sum (p q : Nat) (hp : Prime p) (hq : Prime q)
    (_hne : p ≠ q) : divisorSum (p*q)=p*q := by
  /-
  Lemma: For distinct primes p,q, the totient sum over divisors
  of pq is pq. Proof: The product is positive, so counting its
  reduced fractions gives the formula. Distinctness is retained
  to state the two-prime case, though the counting proof does not
  require it. QED
  -/
  exact totient_divisor_sum _ (Nat.mul_pos (by have := hp.1; omega) (by have := hq.1; omega))

theorem divisor_sum_multiply (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    divisorSum m * divisorSum n=divisorSum (m*n) := by
  /-
  Lemma: The divisor sum is multiplicative, in particular for
  relatively prime positive inputs. Proof: The reduced-fraction
  proof evaluates the two sums on the left as m and n, and the
  sum on the right as mn. Hence both sides are mn. This proves
  the stated coprime case and also shows that this particular
  sum does not require coprimality. No multiplicativity formula
  for phi itself is used. QED
  -/
  rw [totient_divisor_sum m hm,totient_divisor_sum n hn,
    totient_divisor_sum (m*n) (Nat.mul_pos hm hn)]

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

theorem sum_on_zero (ds : List Nat) : sumOn ds (fun _ => 0)=0 := by
  /-
  Lemma: A sum of zeros is zero.
  Proof: Induction adds one zero at a time. QED
  -/
  induction ds with
  | nil => rfl
  | cons _d ds ih => simp only [sumOn,ih,Nat.zero_add]

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

def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a-b

local notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

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

end NumberTheory.DivisorCounts
