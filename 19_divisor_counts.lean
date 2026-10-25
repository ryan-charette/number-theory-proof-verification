import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «12_modular_powers»
import «13_power_cycles»
import «15_reduced_residues»
import «18_order_counts»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.DivisorCounts

open NumberTheory.CommonDivisors (gcd gcd_data gcd_positive gcd_scale)
open NumberTheory.ReducedResidues (phi reducedResidues reduced_mem reduced_nodup same_members_perm)
open NumberTheory.Factorization (Prime)
open NumberTheory (Congruent)
open NumberTheory.PolynomialResidues (bounded_congruent_equal)
open NumberTheory.ModularPowers (gcd_one_right order order_spec)
open NumberTheory.OrderCounts (PrimitiveRoot order_count)
open NumberTheory.PowerCycles (fermat_coprime order_dvd_iff small_prime_coprime)


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

theorem order_class_total (p : Nat) (hp : Prime p) :
    sumOn (divisors (p-1)) (fun d => (orderClass p d).length)=p-1 := by
  /-
  Lemma: Summing the order counts over divisors of p-1 gives p-1.
  Proof: Each nonzero representative is coprime to p. Fermat's
  theorem and the order divisibility criterion put its positive
  order among these divisors. Sorting the p-1 representatives by
  this unique order counts each of them once. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hn' : 0 < p-1 := by have := hp.1; omega
  have h := count_by_labels (positiveRange (p-1)) (divisors (p-1))
    (fun a => order (a : Int) p) (divisors_nodup (p-1)) (by
      intro a ha
      have ha' := (positive_range_mem (p-1) a).mp ha
      have hc := small_prime_coprime p a hp ha'.1 (by have := hp.1; omega)
      apply (divisors_mem (p-1) _ hn').mpr
      exact ⟨(order_spec a p hn hc).1,
        (order_dvd_iff a p hn hc (p-1)).mp (fermat_coprime a p hp hc)⟩)
  simpa only [orderClass,positiveRange,List.length_map,List.length_range] using h

theorem exact_order_count (p d : Nat) (hp : Prime p) (hd : 0 < d)
    (hdp : d ∣ p-1) : (orderClass p d).length=phi d := by
  /-
  Theorem: For every positive divisor d of p-1 there are exactly
  phi(d) residue classes of order d modulo p.
  Proof: Each order count is at most phi(d). Their sum is p-1,
  and the sum of phi(d) over the same divisors is also p-1.
  A strict inequality for any one term would make the total
  strictly smaller. Thus all the individual bounds are equalities.
  QED
  -/
  have hn : 0 < p-1 := by have := hp.1; omega
  apply equal_sum_forces_equal_terms (divisors (p-1))
    (fun e => (orderClass p e).length) phi (fun e _ => order_class_bound p e hp)
  · rw [order_class_total p hp]
    exact (totient_divisor_sum (p-1) hn).symm
  · exact (divisors_mem (p-1) d hn).mpr ⟨hd,hdp⟩

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

theorem primitive_class_mem (p a : Nat) (hp : Prime p) :
    a ∈ orderClass p (p-1) ↔ 0 < a ∧ a < p ∧ PrimitiveRoot a p := by
  /-
  Lemma: The representatives of order p-1 are exactly the
  primitive-root representatives. Proof: Every positive integer
  below a prime is coprime to it. The remaining defining condition
  is that its order be p-1, which is exactly the filter condition.
  QED
  -/
  constructor
  · intro ha
    have h := (order_class_mem p (p-1) a).mp ha
    have hap : a < p := by have := hp.1; omega
    exact ⟨h.1,hap,small_prime_coprime p a hp h.1 hap,h.2.2⟩
  · intro ha
    exact (order_class_mem p (p-1) a).mpr ⟨ha.1,by omega,ha.2.2.2⟩

theorem primitive_root_count (p : Nat) (hp : Prime p) :
    (orderClass p (p-1)).length=phi (p-1) := by
  /-
  Theorem: A prime p has exactly phi(p-1) primitive-root classes.
  Proof: The positive representatives below p with order p-1
  represent precisely these classes. Since p-1 is a positive
  divisor of itself, its order count is phi(p-1). Counting classes
  is essential: adding multiples of p gives infinitely many
  integer representatives of the same primitive root. QED
  -/
  exact exact_order_count p (p-1) hp (by have := hp.1; omega) (Nat.dvd_refl _)

theorem primitive_root_exists (p : Nat) (hp : Prime p) :
    ∃ a : Nat, 0 < a ∧ a < p ∧ PrimitiveRoot a p := by
  /-
  Theorem: Every prime has a primitive root.
  Proof: The list of primitive-root representatives has length
  phi(p-1), which is positive because p-1≥1. Hence the list is
  nonempty. Any of its entries supplies the required root. This
  includes p=2, whose primitive-root representative is one. QED
  -/
  have hpos := phi_positive (p-1) (by have := hp.1; omega)
  have hlen := primitive_root_count p hp
  cases he : orderClass p (p-1) with
  | nil => rw [he] at hlen; simp only [List.length_nil] at hlen; omega
  | cons a xs =>
    exact ⟨a,(primitive_class_mem p a hp).mp (by rw [he]; simp)⟩

end NumberTheory.DivisorCounts
