import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «12_modular_powers»
import «13_power_cycles»
import «15_reduced_residues»
import «23_square_classes»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ResidueSigns

open NumberTheory.ModularPowers (cancel_coprime power_add)
open NumberTheory.PowerCycles (coprime_product distinct_subset_perm intProduct prime_coprime product_congruent product_perm scaled_product small_prime_coprime)
open NumberTheory.Factorization (Prime)
open NumberTheory.SquareClasses (euler_sign minus_one_sign neg_one_power odd_prime_data squareSign)
open NumberTheory (Congruent modeq_add modeq_refl modeq_symm modeq_trans)
open NumberTheory.CommonDivisors (gcd)
open NumberTheory.PolynomialResidues (bounded_congruent_equal)
open NumberTheory.ReducedResidues (factorial factorial_product prime_product_divides)


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

theorem gauss_sign (p : Nat) (a : Int) (r : Nat → Int)
    (hp : Prime p) (ho : p%2=1) (ha : ¬ (p : Int) ∣ a)
    (hr : ∀ i<(p-1)/2, Congruent (r i) (((i : Int)+1)*a) p)
    (hb : ∀ i<(p-1)/2, -((p-1)/2 : Nat) ≤ r i ∧ r i ≤ ((p-1)/2 : Nat)) :
    squareSign a p=(-1 : Int)^(negativeCount ((List.range ((p-1)/2)).map r)) := by
  /-
  Theorem: The sign of a modulo an odd prime equals minus one
  raised to the number of negative centered representatives
  among a,2a,...,ha.
  Proof: Their product is (-1)^g*h! by the preceding theorem.
  Multiplying the original list gives a^h*h!. Congruence of
  corresponding factors makes these products congruent.
  Cancel h!, which is coprime to p, and use Euler's criterion.
  The resulting congruence between two signs is equality. QED
  -/
  have hn : 0 < (p : Int) := by have := hp.1; omega
  have ht := product_congruent (List.range ((p-1)/2)) r
    (fun i : Nat => ((i : Int)+1)*a) p hn (by intro i hi; exact hr i (List.mem_range.mp hi))
  rw [centered_product p a r hp ho ha hr hb] at ht
  have he : intProduct ((List.range ((p-1)/2)).map (fun i : Nat => ((i : Int)+1)*a))=
      a^((p-1)/2)*factorial ((p-1)/2) := by
    have h := scaled_product ((List.range ((p-1)/2)).map (fun i : Nat => i+1)) a
    rw [List.length_map,List.length_range,←factorial_product] at h
    simpa only [List.map_map,Function.comp_def,Int.natCast_add,Int.natCast_one] using h
  rw [he] at ht
  have hc := cancel_coprime _ _ (factorial ((p-1)/2)) p (half_factorial_coprime p hp ho) ht
  have heuler := euler_sign a p hp ho ha
  have hsign := modeq_trans _ _ _ p hc heuler
  apply Eq.symm
  apply sign_congruent_equal _ _ p hp ho ?_ ?_ hsign
  · rw [neg_one_power]
    split <;> simp
  · unfold squareSign
    split <;> simp

def centered (x : Int) (p : Nat) : Int :=
  if x % (p : Int) ≤ ((p-1)/2 : Nat) then x % (p : Int) else x % (p : Int)-p

theorem centered_spec (x : Int) (p : Nat) (hp : Prime p) (ho : p%2=1) :
    Congruent (centered x p) x p ∧
    -((p-1)/2 : Nat) ≤ centered x p ∧ centered x p ≤ ((p-1)/2 : Nat) := by
  /-
  Lemma: Choosing the ordinary remainder if it is at most h,
  and subtracting p otherwise, gives a congruent integer in
  [-h,h]. Proof: The ordinary remainder is between zero and
  p-1=2h. Subtracting p from an entry above h places it between
  -h and -1. Either adjustment changes x by a multiple of p. QED
  -/
  have hn : 0 < (p : Int) := by have := hp.1; omega
  have hh := odd_prime_data p hp ho
  have hlo := Int.emod_nonneg x (by omega : (p : Int)≠0)
  have hhi := Int.emod_lt_of_pos x hn
  have hd := Int.emod_add_ediv x p
  unfold centered
  split
  · rename_i h
    refine ⟨⟨hn,-(x/(p : Int)),?_⟩,by omega,by omega⟩
    rw [Int.mul_neg]
    omega
  · rename_i h
    refine ⟨⟨hn,-(x/(p : Int))-1,?_⟩,by omega,by omega⟩
    rw [Int.mul_sub,Int.mul_neg,Int.mul_one]
    omega

theorem gauss_centered (p : Nat) (a : Int) (hp : Prime p) (ho : p%2=1)
    (ha : ¬ (p : Int) ∣ a) :
    squareSign a p=(-1 : Int)^(negativeCount
      ((List.range ((p-1)/2)).map (fun i : Nat => centered (((i : Int)+1)*a) p))) := by
  /-
  Corollary: Gauss's sign formula applies to the explicit centered
  remainder choice. Proof: Its bounds and congruence property
  are supplied by the centered-remainder lemma. QED
  -/
  apply gauss_sign p a _ hp ho ha
  · intro i _; exact (centered_spec _ p hp ho).1
  · intro i _; exact (centered_spec _ p hp ho).2

theorem negative_count_append (xs ys : List Int) :
    negativeCount (xs++ys)=negativeCount xs+negativeCount ys := by
  /-
  Lemma: Concatenating lists adds their negative counts.
  Proof: Induction on the first list separates its first sign
  contribution and applies the induction hypothesis to the tail. QED
  -/
  induction xs with
  | nil => simp [negativeCount]
  | cons x xs ih => simp [negativeCount,ih,Nat.add_assoc]

theorem negative_range_count (r : Nat → Int) (n t : Nat)
    (h : ∀ i<n, r i<0 ↔ t<i+1) :
    negativeCount ((List.range n).map r)=n-t := by
  /-
  Lemma: If the negative entries are exactly the positions after
  t in a list of n positions, their number is n-t, truncated at
  zero. Proof: Append one position at a time. Positions up to t
  contribute nothing; each subsequent position contributes one. QED
  -/
  induction n with
  | zero => simp [negativeCount]
  | succ n ih =>
    have ht := ih (fun i hi => h i (by omega))
    rw [List.range_succ,List.map_append,negative_count_append,ht]
    simp only [List.map_cons,List.map_nil,negativeCount,Nat.add_zero]
    by_cases hn : t<n+1
    · rw [if_pos ((h n (by omega)).mpr hn)]
      omega
    · have hn' : ¬ r n<0 := fun hr => hn ((h n (by omega)).mp hr)
      rw [if_neg hn']
      omega

theorem doubled_centered_negative (p i : Nat) (hp : Prime p) (ho : p%2=1)
    (hi : i<(p-1)/2) : centered (((i : Int)+1)*2) p<0 ↔ p/4<i+1 := by
  /-
  Lemma: The centered representative of 2(i+1) is negative
  precisely when i+1 exceeds p/4.
  Proof: These doubled entries lie strictly between zero and p,
  so they already are ordinary remainders. Centering subtracts
  p exactly when the entry exceeds (p-1)/2, equivalently when
  its position exceeds p/4. QED
  -/
  have hh := odd_prime_data p hp ho
  have he : (((i : Int)+1)*2) % (p : Int)=((i : Int)+1)*2 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  unfold centered
  rw [he]
  split <;> omega

theorem two_square_sign (p : Nat) (hp : Prime p) (ho : p%2=1) :
    (p%8=1 ∨ p%8=7 → squareSign 2 p=1) ∧
    (p%8=3 ∨ p%8=5 → squareSign 2 p= -1) := by
  /-
  Theorem: Two has sign one for primes with remainder one or
  seven modulo eight, and sign minus one for remainders three
  or five.
  Proof: Gauss's lemma counts h-floor(p/4) negative entries in
  the doubled half-list. For remainders one and seven this
  count is even; for three and five it is odd. Substitute
  these parities in the sign formula. QED
  -/
  have hh := odd_prime_data p hp ho
  have hg := gauss_centered p 2 hp ho hh.2.2
  have hc := negative_range_count (fun i => centered (((i : Int)+1)*2) p)
    ((p-1)/2) (p/4) (fun i hi => doubled_centered_negative p i hp ho hi)
  rw [hc,neg_one_power] at hg
  constructor
  · intro hr
    have he : (((p-1)/2)-(p/4))%2=0 := by rcases hr with h|h <;> omega
    simpa only [if_pos he] using hg
  · intro hr
    have he : (((p-1)/2)-(p/4))%2≠0 := by rcases hr with h|h <;> omega
    simpa only [if_neg he] using hg

def rangeSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => rangeSum n f+f n

theorem range_sum_add (n : Nat) (f g : Nat → Nat) :
    rangeSum n (fun i => f i+g i)=rangeSum n f+rangeSum n g := by
  /-
  Lemma: Summing pointwise sums adds the two sums. Proof:
  Induction separates the last terms and rearranges additions. QED
  -/
  induction n with
  | zero => rfl
  | succ n ih => simp only [rangeSum,ih]; omega

theorem range_sum_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i<n, f i=g i) : rangeSum n f=rangeSum n g := by
  /-
  Lemma: Equal summands give equal finite sums. Proof: Induct
  on the number of summands, using equality of the last terms. QED
  -/
  induction n with
  | zero => rfl
  | succ n ih => rw [rangeSum,rangeSum,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem range_sum_parity (n : Nat) (f g : Nat → Nat)
    (h : ∀ i<n, f i%2=g i%2) : rangeSum n f%2=rangeSum n g%2 := by
  /-
  Lemma: Termwise equal parities give equal parities of sums.
  Proof: Induct and reduce each addition modulo two. QED
  -/
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rangeSum]
    have hi := ih (fun i hi => h i (by omega))
    have he := h n (by omega)
    omega

def listSum : List Nat → Nat
  | [] => 0
  | x::xs => x+listSum xs

theorem list_sum_append (xs ys : List Nat) : listSum (xs++ys)=listSum xs+listSum ys := by
  /-
  Lemma: Concatenation adds sums. Proof: Induct on the first list
  and associate the addition of its first term. QED
  -/
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum,ih,Nat.add_assoc]

theorem range_sum_list (n : Nat) (f : Nat → Nat) :
    rangeSum n f=listSum ((List.range n).map f) := by
  /-
  Lemma: Recursive summation agrees with summing a mapped range.
  Proof: Appending the final index appends its summand, exactly
  the recursive rule for the sum. QED
  -/
  induction n with
  | zero => rfl
  | succ n ih => simp [rangeSum,List.range_succ,list_sum_append,listSum,ih]

theorem list_sum_perm (xs ys : List Nat) (h : xs.Perm ys) : listSum xs=listSum ys := by
  /-
  Lemma: Rearranging a list preserves its sum. Proof: Adding a
  common first term preserves equality, swapping adjacent terms
  uses commutativity, and successive rearrangements compose. QED
  -/
  induction h with
  | nil => rfl
  | cons a _h ih => simp [listSum,ih]
  | swap a b xs => simp [listSum,Nat.add_left_comm]
  | trans _h1 _h2 ih1 ih2 => exact ih1.trans ih2

theorem negative_count_sum (n : Nat) (r : Nat → Int) :
    negativeCount ((List.range n).map r)=rangeSum n (fun i => if r i<0 then 1 else 0) := by
  /-
  Lemma: The negative count is the sum of the negative-entry
  indicators. Proof: Appending one entry adds its indicator
  to either expression. Induction proves equality. QED
  -/
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.range_succ,negative_count_append,negativeCount,rangeSum,ih]

theorem floor_parity_term (p a i : Nat) (hp : Prime p) (ho : p%2=1) (hao : a%2=1) :
    (((i+1)*a)/p+(if centered (((i+1)*a : Nat) : Int) p<0 then 1 else 0)+
      magnitude (centered (((i+1)*a : Nat) : Int) p))%2=(i+1)%2 := by
  /-
  Lemma: For odd a and p, the quotient, centering sign, and
  centered magnitude together have the parity of the position.
  Proof: Write a(i+1)=p*q+m with 0<=m<p. Modulo two this gives
  q+m congruent to i+1. Centering either leaves m unchanged,
  or replaces it by magnitude p-m and adds one sign. Since
  p is odd, 1+p-m has the same parity as m. QED
  -/
  let x := (i+1)*a
  let m := x%p
  have hn : 0 < p := by have := hp.1; omega
  have hm : m<p := Nat.mod_lt x hn
  have hd := congrArg (fun k : Nat => k%2) (Nat.mod_add_div x p)
  have hrel : (m+x/p)%2=(i+1)%2 := by
    simpa only [x,m,Nat.add_mod,Nat.mul_mod,ho,hao,Nat.one_mul,Nat.mul_one,Nat.mod_mod] using hd
  have hc : centered (x : Int) p=
      if m≤(p-1)/2 then (m : Int) else (m : Int)-p := by
    simp only [centered,←Int.ofNat_emod,m]
    split <;> split <;> omega
  change (x/p+(if centered (x : Int) p<0 then 1 else 0)+magnitude (centered (x : Int) p))%2=_
  have hv := magnitude_cast (centered (x : Int) p)
  by_cases h : m≤(p-1)/2
  · rw [hc,if_pos h] at hv ⊢
    have hnon : ¬ (m : Int)<0 := by omega
    rw [if_neg hnon] at hv ⊢
    have he : magnitude (m : Int)=m := by omega
    rw [he]
    omega
  · rw [hc,if_neg h] at hv ⊢
    have hneg : (m : Int)-p<0 := by omega
    rw [if_pos hneg] at hv ⊢
    have he : magnitude ((m : Int)-p)=p-m := by omega
    rw [he]
    omega

def floorSum (a p : Nat) : Nat := rangeSum ((p-1)/2) (fun i => ((i+1)*a)/p)

theorem gauss_floor_sign (p a : Nat) (hp : Prime p) (ho : p%2=1)
    (hao : a%2=1) (ha : ¬ (p : Int) ∣ a) :
    squareSign a p=(-1 : Int)^(floorSum a p) := by
  /-
  Theorem: For an odd positive multiplier, the sign is minus one
  raised to the sum of the quotients floor(ai/p), for 1<=i<=h.
  Proof: Sum the termwise parity identity. The centered magnitudes
  rearrange 1,...,h, so their sum equals the sum of the positions
  and cancels modulo two. The quotient sum and negative count
  thus have equal parity. Gauss's lemma gives the result. QED
  -/
  let r := fun i : Nat => centered (((i+1)*a : Nat) : Int) p
  have hr : ∀ i<(p-1)/2, Congruent (r i) (((i : Int)+1)*(a : Int)) p := by
    intro i _
    simpa only [r,Int.natCast_mul,Int.natCast_add,Int.natCast_one] using
      (centered_spec (((i+1)*a : Nat) : Int) p hp ho).1
  have hb : ∀ i<(p-1)/2, -((p-1)/2 : Nat) ≤ r i ∧ r i ≤ ((p-1)/2 : Nat) :=
    fun i _ => (centered_spec _ p hp ho).2
  have hm := list_sum_perm _ _ (centered_magnitudes_perm p a r hp ho (prime_coprime a p hp ha) hr hb)
  rw [←range_sum_list,←range_sum_list] at hm
  have ht := range_sum_parity ((p-1)/2)
    (fun i => ((i+1)*a)/p+(if r i<0 then 1 else 0)+magnitude (r i)) (fun i => i+1)
    (fun i _ => floor_parity_term p a i hp ho hao)
  rw [range_sum_add,range_sum_add,hm,←negative_count_sum] at ht
  have he : negativeCount ((List.range ((p-1)/2)).map r)%2=floorSum a p%2 := by
    unfold floorSum
    omega
  rw [gauss_sign p a r hp ho ha hr hb,neg_one_power,neg_one_power,he]

theorem prime_cross_not_divides (p q i : Nat) (hp : Prime p) (hq : Prime q)
    (hne : p≠q) (hi : i+1<p) : ¬ p ∣ q*(i+1) := by
  /-
  Lemma: A prime p distinct from q does not divide q(i+1) when
  1<=i+1<p. Proof: Divisibility of the product forces p to
  divide q or i+1. Primality excludes the first alternative,
  and the positive bound excludes the second. QED
  -/
  intro h
  have hd : (p : Int) ∣ (q : Int)*((i+1 : Nat) : Int) := by
    simpa only [Int.natCast_mul] using Int.ofNat_dvd.mpr h
  rcases prime_product_divides p q ((i+1 : Nat) : Int) hp hd with hq' | hi'
  · rcases hq.2 p (Int.ofNat_dvd.mp hq') with h1 | he
    · have := hp.1; omega
    · exact hne he
  · have hb := Nat.le_of_dvd (by omega : 0<i+1) (Int.ofNat_dvd.mp hi')
    omega

theorem half_floor_bound (p q i : Nat) (hp : Prime p) (hq : Prime q)
    (hpo : p%2=1) (hqo : q%2=1) (hi : i<(p-1)/2) :
    (q*(i+1))/p ≤ (q-1)/2 := by
  /-
  Lemma: The row quotient stays within the half-height rectangle.
  Proof: Put m=(p-1)/2 and n=(q-1)/2. Since i+1<=m,
    q(i+1)<=qm<(n+1)p.
  The strict inequality follows by expanding p=2m+1 and q=2n+1.
  Division by positive p therefore gives quotient at most n. QED
  -/
  let m := (p-1)/2
  let n := (q-1)/2
  have hpm := odd_prime_data p hp hpo
  have hqn := odd_prime_data q hq hqo
  have heP : p=2*m+1 := by dsimp [m]; omega
  have heQ : q=2*n+1 := by dsimp [n]; omega
  have hle : q*(i+1) ≤ q*m := Nat.mul_le_mul_left q (by dsimp [m]; omega)
  have hlt : q*m<(n+1)*p := by
    rw [heP,heQ]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    have he : 2*n*m=n*(2*m) := by simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [he]
    omega
  have hd := (Nat.div_lt_iff_lt_mul (by have := hp.1; omega : 0<p)).mpr (Nat.lt_of_le_of_lt hle hlt)
  dsimp [n] at hd
  omega

theorem strict_multiple_quotient (p x j : Nat) (hp : 0<p) (hx : ¬ p ∣ x) :
    p*(j+1)<x ↔ j<x/p := by
  /-
  Lemma: When x is not divisible by p, positive multiples below
  x are indexed by j<x/p. Proof: The division inequality gives
  (j+1)p<=x exactly when j+1<=floor(x/p). Equality of the multiple
  with x is excluded by the nondivisibility hypothesis. QED
  -/
  constructor
  · intro h
    have he : (j+1)*p≤x := by rw [Nat.mul_comm]; omega
    have := (Nat.le_div_iff_mul_le hp).mpr he
    omega
  · intro h
    have he := (Nat.le_div_iff_mul_le hp).mp (by omega : j+1≤x/p)
    have hn : p*(j+1)≠x := fun he => hx ⟨j+1,he.symm⟩
    rw [Nat.mul_comm] at he
    omega

theorem range_count_below (n t : Nat) :
    rangeSum n (fun j => if j<t then 1 else 0)=min n t := by
  /-
  Lemma: Among indices 0,...,n-1 exactly min(n,t) lie below t.
  Proof: Append index n. It contributes one precisely when n<t.
  Induction gives the stated count in either case. QED
  -/
  induction n with
  | zero => simp [rangeSum]
  | succ n ih =>
    rw [rangeSum,ih]
    by_cases h : n<t
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

theorem lattice_row_count (p q i : Nat) (hp : Prime p) (hq : Prime q)
    (hpo : p%2=1) (hqo : q%2=1) (hne : p≠q) (hi : i<(p-1)/2) :
    rangeSum ((q-1)/2) (fun j => if p*(j+1)<q*(i+1) then 1 else 0)=q*(i+1)/p := by
  /-
  Lemma: The number of lattice points below the diagonal in row
  i+1 is floor(q(i+1)/p). Proof: The strict-multiple criterion
  identifies the qualifying indices. The quotient is at most
  the half-height, so counting these indices gives the quotient. QED
  -/
  have hh := odd_prime_data p hp hpo
  have hdiv := prime_cross_not_divides p q i hp hq hne (by omega)
  have he := range_sum_congr ((q-1)/2)
    (fun j => if p*(j+1)<q*(i+1) then 1 else 0)
    (fun j => if j<q*(i+1)/p then 1 else 0) (by
      intro j _
      dsimp only
      have ht := strict_multiple_quotient p (q*(i+1)) j (by have := hp.1; omega) hdiv
      by_cases h : j<q*(i+1)/p
      · simp [h,ht.mpr h]
      · have hn : ¬p*(j+1)<q*(i+1) := fun hh => h (ht.mp hh)
        simp [h,hn])
  rw [he,range_count_below]
  exact Nat.min_eq_right (half_floor_bound p q i hp hq hpo hqo hi)

theorem range_sum_const (n c : Nat) : rangeSum n (fun _ => c)=n*c := by
  /-
  Lemma: Summing a constant n times gives n times that constant.
  Proof: Induct and use the multiplication successor identity. QED
  -/
  induction n with
  | zero => simp [rangeSum]
  | succ n ih => simp [rangeSum,ih,Nat.succ_mul]

theorem range_sum_swap (m n : Nat) (f : Nat → Nat → Nat) :
    rangeSum m (fun i => rangeSum n (fun j => f i j))=
      rangeSum n (fun j => rangeSum m (fun i => f i j)) := by
  /-
  Lemma: A finite rectangular sum may be taken by rows or columns.
  Proof: Induct on the number of rows. Adding a row adds its
  sum; distribute this addition over the column sums. QED
  -/
  induction m with
  | zero => simp [rangeSum,range_sum_const]
  | succ m ih => simp only [rangeSum,range_sum_add,ih]

theorem rectangle_partition (m n : Nat) (f g : Nat → Nat → Nat)
    (h : ∀ i<m, ∀ j<n, f i j+g i j=1) :
    rangeSum m (fun i => rangeSum n (fun j => f i j))+
      rangeSum m (fun i => rangeSum n (fun j => g i j))=m*n := by
  /-
  Lemma: If two indicators partition every cell of a rectangle,
  their total counts add to its area. Proof: Add their sums
  termwise. Each cell contributes one, so each row contributes
  n and all m rows contribute mn. QED
  -/
  rw [←range_sum_add]
  have he := range_sum_congr m
    (fun i => rangeSum n (fun j => f i j)+rangeSum n (fun j => g i j))
    (fun _ => n) (by
      intro i hi
      dsimp only
      rw [←range_sum_add]
      have hj := range_sum_congr n (fun j => f i j+g i j) (fun _ => 1) (h i hi)
      rw [hj,range_sum_const,Nat.mul_one])
  rw [he,range_sum_const]

theorem floor_sum_reciprocity (p q : Nat) (hp : Prime p) (hq : Prime q)
    (hpo : p%2=1) (hqo : q%2=1) (hne : p≠q) :
    floorSum q p+floorSum p q=((p-1)/2)*((q-1)/2) := by
  /-
  Lemma: The two floor sums add to the area of the half-size
  rectangle. Proof: In the rectangle 1<=i<=h_p, 1<=j<=h_q,
  every point satisfies pj<qi or qi<pj. Equality would make p
  divide qi, impossible for distinct primes and 0<i<p. The
  first region has row counts floor(qi/p); the second has
  column counts floor(pj/q). They partition the rectangle. QED
  -/
  let f := fun i j : Nat => if p*(j+1)<q*(i+1) then 1 else 0
  let g := fun i j : Nat => if q*(i+1)<p*(j+1) then 1 else 0
  have hf : floorSum q p=rangeSum ((p-1)/2) (fun i => rangeSum ((q-1)/2) (fun j => f i j)) := by
    apply range_sum_congr
    intro i hi
    rw [lattice_row_count p q i hp hq hpo hqo hne hi]
    rw [Nat.mul_comm q (i+1)]
  have hg : floorSum p q=rangeSum ((q-1)/2) (fun j => rangeSum ((p-1)/2) (fun i => g i j)) := by
    apply range_sum_congr
    intro j hj
    rw [lattice_row_count q p j hq hp hqo hpo (Ne.symm hne) hj]
    rw [Nat.mul_comm p (j+1)]
  rw [hf,hg,←range_sum_swap ((p-1)/2) ((q-1)/2) g]
  apply rectangle_partition
  intro i hi j _hj
  have hh := odd_prime_data p hp hpo
  have hdiv := prime_cross_not_divides p q i hp hq hne (by omega)
  have hneq : p*(j+1)≠q*(i+1) := fun he => hdiv ⟨j+1,he.symm⟩
  dsimp [f,g]
  split <;> split <;> omega

theorem reciprocity_product (p q : Nat) (hp : Prime p) (hq : Prime q)
    (hpo : p%2=1) (hqo : q%2=1) (hne : p≠q) :
    squareSign q p * squareSign p q = (-1 : Int)^(((p-1)/2)*((q-1)/2)) := by
  /-
  Theorem: For distinct odd primes, the product of the two
  residue signs is minus one raised to the area of the
  half-size rectangle. Proof: Apply the floor-sum form of
  Gauss's lemma to each sign. Multiplying adds the exponents,
  and the lattice-point partition identifies their sum. QED
  -/
  have hqp : ¬ (p : Int) ∣ (q : Int) := by
    intro h
    have hn := prime_cross_not_divides p q 0 hp hq hne (by have := hp.1; omega)
    apply hn
    simpa using Int.ofNat_dvd.mp h
  have hpq : ¬ (q : Int) ∣ (p : Int) := by
    intro h
    have hn := prime_cross_not_divides q p 0 hq hp (Ne.symm hne) (by have := hq.1; omega)
    apply hn
    simpa using Int.ofNat_dvd.mp h
  rw [gauss_floor_sign p q hp hpo hqo hqp,gauss_floor_sign q p hq hqo hpo hpq,
    ←power_add,floor_sum_reciprocity p q hp hq hpo hqo hne]

theorem quadratic_reciprocity (p q : Nat) (hp : Prime p) (hq : Prime q)
    (hpo : p%2=1) (hqo : q%2=1) (hne : p≠q) :
    ((p%4=1 ∨ q%4=1) → squareSign p q=squareSign q p) ∧
    (p%4=3 → q%4=3 → squareSign p q= -squareSign q p) := by
  /-
  Theorem: For distinct odd primes, interchanging numerator
  and modulus preserves the residue sign if either prime is
  one modulo four, and reverses it if both are three modulo
  four. Proof: The half-size rectangle has even area in the
  first case and odd area in the second. The product formula
  therefore gives one or minus one. Since each sign is one
  or minus one, this gives precisely the stated equalities.
  Distinctness excludes a zero residue class. QED
  -/
  have he := reciprocity_product p q hp hq hpo hqo hne
  have hv : squareSign q p=1 ∨ squareSign q p= -1 := by
    unfold squareSign
    split <;> simp
  rw [neg_one_power] at he
  constructor
  · intro h
    have ht : (((p-1)/2)*((q-1)/2))%2=0 := by
      rw [Nat.mul_mod]
      rcases h with h | h
      · have hz : ((p-1)/2)%2=0 := by omega
        simp [hz]
      · have hz : ((q-1)/2)%2=0 := by omega
        simp [hz]
    rw [ht] at he
    simp only [if_pos,if_false,show ¬(1 : Nat)=0 by decide] at he
    rcases hv with hv | hv <;> rw [hv] at he ⊢ <;> simp_all <;> omega
  · intro hp4 hq4
    have ht : (((p-1)/2)*((q-1)/2))%2=1 := by
      rw [Nat.mul_mod]
      have h1 : ((p-1)/2)%2=1 := by omega
      have h2 : ((q-1)/2)%2=1 := by omega
      rw [h1,h2]
    rw [ht] at he
    simp only [if_pos,if_false,show ¬(1 : Nat)=0 by decide] at he
    rcases hv with hv | hv <;> rw [hv] at he ⊢ <;> simp_all <;> omega

theorem residue_sign_rules (p q : Nat) (hp : Prime p) (hq : Prime q)
    (hpo : p%2=1) (hqo : q%2=1) (hne : p≠q) :
    ((p%4=1 → squareSign (-1) p=1) ∧
      (p%4=3 → squareSign (-1) p= -1)) ∧
    ((p%8=1 ∨ p%8=7 → squareSign 2 p=1) ∧
      (p%8=3 ∨ p%8=5 → squareSign 2 p= -1)) ∧
    (((p%4=1 ∨ q%4=1) → squareSign p q=squareSign q p) ∧
      (p%4=3 → q%4=3 → squareSign p q= -squareSign q p)) := by
  /-
  Corollary: The rules for minus one, two, and interchanging
  distinct odd primes hold together. Proof: The minus-one
  criterion gives the first pair of cases. Counting negative
  centered multiples of two gives the second. Quadratic
  reciprocity gives the final pair. All primes here are odd,
  and the two primes in the interchange rule are distinct. QED
  -/
  exact ⟨minus_one_sign p hp hpo,two_square_sign p hp hpo,
    quadratic_reciprocity p q hp hq hpo hqo hne⟩

end NumberTheory.ResidueSigns
