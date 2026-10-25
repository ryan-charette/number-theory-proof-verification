import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «11_simultaneous_congruences»
import «12_modular_powers»
import «15_reduced_residues»
import «19_divisor_counts»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.TotientProducts

open NumberTheory.ReducedResidues (gcd_one_combination phi phi_prime positiveLabel positiveLabel_spec positive_congruent_equal reducedResidues reduced_mem reduced_nodup same_members_perm)
open NumberTheory.CommonDivisors (bezout gcd)
open NumberTheory.Factorization (Prime)
open NumberTheory (Congruent modeq_symm modeq_trans)
open NumberTheory.PolynomialResidues (CompleteResidues Noncongruent bounded_congruent_equal noncongruent_full_length_complete)
open NumberTheory.ModularPowers (cancel_coprime congruent_coprime)
open NumberTheory.SimultaneousCongruences (bezout_product)
open NumberTheory.DivisorCounts (positiveRange positive_range_mem positive_range_nodup)


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

def progression (k m : Int) (n : Nat) : List Int :=
  (List.range n).map (fun j : Nat => k+(j : Int)*m)

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

theorem coprime_count_constant (xs : List Int) (i m : Int)
    (h : ∀ a ∈ xs, gcd a m=1 ↔ gcd i m=1) :
    coprimeCount xs m=if gcd i m=1 then xs.length else 0 := by
  /-
  Lemma: If every entry has the same coprimality status as i,
  the count is the whole length or zero.
  Proof: Induct on the list. In the coprime case every entry
  is kept; in the other case every entry is removed. QED
  -/
  induction xs with
  | nil => simp [coprimeCount]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    by_cases hi : gcd i m=1
    · have ha' := ha.mpr hi
      have ht' : coprimeCount xs m=xs.length := by simpa only [if_pos hi] using ht
      simpa [coprimeCount,hi,ha'] using congrArg Nat.succ ht'
    · have ha' : gcd a m ≠ 1 := fun ha' => hi (ha.mp ha')
      simpa [coprimeCount,hi,ha'] using ht

theorem coprime_count_append (xs ys : List Int) (n : Int) :
    coprimeCount (xs++ys) n=coprimeCount xs n+coprimeCount ys n := by
  /-
  Lemma: Counts add when lists are appended.
  Proof: Filtering an append filters both parts, and the length
  of their append is the sum of their lengths. QED
  -/
  simp only [coprimeCount,List.filter_append,List.length_append]

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

theorem column_base_count (i : Int) (m n : Nat) (hm : 0 < m) :
    coprimeCount (progression i m n) m=if gcd i m=1 then n else 0 := by
  /-
  Lemma: Counting entries coprime to m in one column gives n
  or zero according as its starting value is coprime or not.
  Proof: Every entry has the same coprimality status with m,
  and there are n positions in the column. QED
  -/
  rw [coprime_count_constant _ i m (column_coprime_iff i m n hm)]
  simp only [progression,List.length_map,List.length_range]

theorem grid_base_count (m n : Nat) (hm : 0 < m) (is : List Nat) :
    coprimeCount (gridRows m n is) m =
      n*(is.filter (fun i : Nat => decide (gcd (i : Int) m=1))).length := by
  /-
  Lemma: Counting array entries coprime to its width m gives
  n times the number of coprime column starts.
  Proof: A qualifying column contributes all n entries; any
  other column contributes zero. Append the columns and add
  their counts by induction. QED
  -/
  induction is with
  | nil => simp [gridRows,coprimeCount]
  | cons i is ih =>
    rw [gridRows,coprime_count_append,column_base_count i m n hm,ih]
    by_cases hi : gcd (i : Int) m=1
    · simp [hi,Nat.mul_add,Nat.add_comm]
    · simp [hi]

theorem phi_prime_power (p k : Nat) (hp : Prime p) :
    phi (p^(k+1))=p^(k+1)-p^k := by
  /-
  Theorem: Phi of the positive power p^(k+1) is p^(k+1)-p^k.
  Proof: Arrange the p^(k+1) representatives in p columns of
  height p^k. Coprimality to p^(k+1) is exactly coprimality to p.
  Each column has constant remainder modulo p. The p-1 columns
  starting at 1,...,p-1 qualify; the column starting at p consists
  of the multiples of p and does not. Thus the count is
  p^k*(p-1)=p^(k+1)-p^k. Writing the exponent as k+1 expresses
  its positivity; exponent zero is covered by phi(1)=1. QED
  -/
  have hpp : 0 < p := by have := hp.1; omega
  have hpow : 0 < p^k := Nat.pow_pos hpp
  have he : p*p^k=p^(k+1) := by rw [Nat.pow_succ,Nat.mul_comm]
  have hcount := complete_coprime_count (gridRows p (p^k) (positiveRange p)) (p*p^k)
    (Nat.mul_pos hpp hpow) (grid_complete p (p^k) hpp hpow)
  have hc : coprimeCount (gridRows p (p^k) (positiveRange p)) (p*p^k : Nat)=
      coprimeCount (gridRows p (p^k) (positiveRange p)) p := by
    apply coprime_count_congr
    intro a _
    rw [he,Int.natCast_pow]
    exact coprime_power_iff a p k
  rw [hc,grid_base_count p (p^k) hpp] at hcount
  change p^k * phi p=phi (p*p^k) at hcount
  rw [phi_prime p hp,he] at hcount
  rw [← hcount,Nat.mul_sub_left_distrib,Nat.mul_one,Nat.pow_succ]

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

end NumberTheory.TotientProducts
