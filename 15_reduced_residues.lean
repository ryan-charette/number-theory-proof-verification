import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «05_divisibility_tests»
import «09_polynomial_residues»
import «12_modular_powers»
import «13_power_cycles»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ReducedResidues

open NumberTheory.CommonDivisors (bezout divisor_le_positive dvd_linear gcd gcd_data)
open NumberTheory (Congruent modeq_mult modeq_refl modeq_symm modeq_trans)
open NumberTheory.PolynomialResidues (bounded_congruent_equal canonicalLabel canonicalLabel_spec)
open NumberTheory.ModularPowers (cancel_coprime congruent_coprime)
open NumberTheory.Factorization (Prime)
open NumberTheory.PowerCycles (coprime_product distinct_subset_perm intProduct nonzeroResidues nonzero_residues_mem prime_coprime product_congruent product_perm scaled_product small_prime_coprime)
open NumberTheory.DivisibilityTests (distinct_length_bound)


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

noncomputable def reducedResidues (n : Nat) : List Nat := by
  exact ((List.range n).map (fun i => i+1)).filter (fun i => decide (gcd (i : Int) n=1))

noncomputable def phi (n : Nat) : Nat := (reducedResidues n).length

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
    (NumberTheory.CommonDivisors.coprime_product i a n ((reduced_mem n i).mp hi).2.2 hc) hs.2.2⟩

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

theorem fermat_from_euler (a : Int) (p : Nat) (hp : Prime p) (hc : gcd a p=1) :
    Congruent (a^(p-1)) 1 p := by
  /-
  Corollary: Fermat's congruence follows from Euler's theorem.
  Proof: For a prime the reduced-residue count is p-1. Substitute
  this count into Euler's exponent. QED
  -/
  have h := euler_power a p (by have := hp.1; omega) hc
  rw [phi_prime p hp] at h
  exact h

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

theorem inverse_exists_unique (p a : Nat) (hp : Prime p) (ha : 0 < a) (hap : a < p) :
    ∃ b : Nat, 0 < b ∧ b < p ∧ Congruent ((a : Int)*b) 1 p ∧
      ∀ c : Nat, 0 < c → c < p → Congruent ((a : Int)*c) 1 p → c=b := by
  /-
  Theorem: Every positive representative below a prime has exactly
  one inverse in that range. Proof: Choose a*u+p*v=1 by Bezout
  and reduce u to its canonical label b. Multiplication preserves
  congruence, so a*b is congruent to one. The label cannot be zero,
  since zero and one are different canonical representatives.
  If c is another inverse, cancel a from a*c congruent to a*b;
  bounded representatives are then equal. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hc := small_prime_coprime p a hp ha hap
  rcases bezout (a : Int) p with ⟨u,v,he⟩
  rw [hc] at he
  let b := canonicalLabel u p
  have hs := canonicalLabel_spec u p hn
  have hu : Congruent ((a : Int)*u) 1 p := by
    refine ⟨by omega,-v,?_⟩
    rw [Int.mul_neg]; omega
  have hm := modeq_mult (a : Int) a u b p (modeq_refl _ _ (by omega)) hs.2
  have hb := modeq_trans _ _ _ p (modeq_symm _ _ p hm) hu
  have hbpos : 0 < b := by
    by_cases hz : b=0
    · rw [hz,Int.natCast_zero,Int.mul_zero] at hb
      have hf := bounded_congruent_equal 0 1 p (by omega) (by omega) (by omega)
        (by have := hp.1; omega) hb
      omega
    · omega
  refine ⟨b,hbpos,hs.1,hb,?_⟩
  intro c hcpos hcp hcinv
  have hprod := modeq_trans _ _ _ p hcinv (modeq_symm _ _ p hb)
  have hcancel := cancel_coprime c b a p hc (by simpa only [Int.mul_comm] using hprod)
  have heq := bounded_congruent_equal c b p (by omega) (by omega) (by omega) (by omega) hcancel
  omega

theorem endpoint_inverses (p : Nat) (hp : Prime p) :
    Congruent ((1 : Int)*1) 1 p ∧ Congruent (((p : Int)-1)*((p : Int)-1)) 1 p := by
  /-
  Theorem: One and p-1 are their own inverses modulo a prime.
  Proof: The first product is one. For the second, subtracting one
  from (p-1)^2 gives p*(p-2), an explicit multiple of p. QED
  -/
  constructor
  · simpa using modeq_refl 1 p (by have := hp.1; omega)
  · refine ⟨by have := hp.1; omega,(p : Int)-2,?_⟩
    simp only [Int.mul_sub,Int.sub_mul,Int.one_mul,Int.mul_one]
    omega

theorem self_inverse_endpoints (p : Nat) (a : Int) (hp : Prime p) (ha : 0 < a)
    (hap : a < p) (h : Congruent (a*a) 1 p) : a=1 ∨ a=(p : Int)-1 := by
  /-
  Lemma: A self-inverse representative modulo a prime is one or
  p-1. Proof: Factor a*a-1=(a-1)*(a+1). The prime divides one
  factor. If it divides a-1, that factor lies between zero and
  p-1 and must be zero. If it divides a+1, the positive factor
  lies at most p and is congruent to p, so it equals p. QED
  -/
  have hd : (p : Int) ∣ (a-1)*(a+1) := by
    have he : (a-1)*(a+1)=a*a-1 := by
      simp only [Int.sub_mul,Int.mul_add,Int.mul_one,Int.one_mul]; omega
    rw [he]; exact h.2
  rcases prime_product_divides p (a-1) (a+1) hp hd with h₁ | h₂
  · have hc : Congruent (a-1) 0 p := ⟨h.1,by simpa using h₁⟩
    have he := bounded_congruent_equal (a-1) 0 p (by omega) (by omega) (by omega) (by omega) hc
    exact Or.inl (by omega)
  · rcases h₂ with ⟨q,hq⟩
    have hc : Congruent (a+1) p p := by
      refine ⟨h.1,q-1,?_⟩
      rw [Int.mul_sub,Int.mul_one]; omega
    have he := positive_congruent_equal (a+1) p p (by omega) (by omega) (by omega) (by omega) hc
    exact Or.inr (by omega)

theorem interior_inverses_distinct (p : Nat) (a b : Int) (hp : Prime p)
    (ha : 1 < a) (hap : a < (p : Int)-1) (h : Congruent (a*b) 1 p) : a ≠ b := by
  /-
  Theorem: An interior representative cannot equal its inverse.
  Proof: Equality would make it self-inverse. Such a representative
  is either one or p-1, both excluded by the strict bounds. QED
  -/
  intro he
  subst b
  rcases self_inverse_endpoints p a hp (by omega) (by omega) h with h₁ | h₂ <;> omega

theorem prime_inverse_unique (p a b c : Nat) (hp : Prime p)
    (ha : 0 < a) (hap : a < p) (hb : b < p) (hc : c < p)
    (hab : Congruent ((a : Int)*b) 1 p) (hac : Congruent ((a : Int)*c) 1 p) : b=c := by
  /-
  Lemma: Two canonical inverses of the same nonzero representative
  are equal. Proof: Their products with a are congruent to each
  other. Cancel a, which is coprime to the prime, and use uniqueness
  of representatives between zero and p-1. QED
  -/
  have hm := modeq_trans _ _ _ p hab (modeq_symm _ _ p hac)
  have hd := cancel_coprime b c a p (small_prime_coprime p a hp ha hap)
    (by simpa only [Int.mul_comm] using hm)
  have he := bounded_congruent_equal b c p (by omega) (by omega) (by omega) (by omega) hd
  omega

theorem interior_inverse_exists (p a : Nat) (hp : Prime p)
    (ha : 1 < a) (hap : a < p-1) :
    ∃ b : Nat, 1 < b ∧ b < p-1 ∧ b ≠ a ∧ Congruent ((a : Int)*b) 1 p := by
  /-
  Lemma: Each interior representative has a different inverse
  in the interior. Proof: Take its unique positive inverse b.
  If b were one, its product with a would force a=1. If b were
  p-1, both a and p-1 would invert p-1, forcing a=p-1.
  Neither endpoint is allowed. Equality b=a is excluded by the
  classification of self-inverse representatives. QED
  -/
  have hp1 := hp.1
  rcases inverse_exists_unique p a hp (by omega) (by omega) with ⟨b,hb,hbp,hab,_⟩
  have hb1 : b ≠ 1 := by
    intro he
    have hm : Congruent (a : Int) 1 p := by simpa [he] using hab
    have heq := bounded_congruent_equal a 1 p (by omega) (by omega) (by omega) (by omega) hm
    omega
  have hblast : b ≠ p-1 := by
    intro he
    have hend : Congruent (((p-1 : Nat) : Int)*(p-1 : Nat)) 1 p := by
      have hcast : ((p-1 : Nat) : Int)=(p : Int)-1 := by omega
      rw [hcast]; exact (endpoint_inverses p hp).2
    have hm : Congruent (((p-1 : Nat) : Int)*a) 1 p := by
      simpa only [he,Int.mul_comm] using hab
    have heq := prime_inverse_unique p (p-1) a (p-1) hp (by omega) (by omega)
      (by omega) (by omega) hm hend
    omega
  refine ⟨b,by omega,by omega,?_,hab⟩
  intro he
  have hne := interior_inverses_distinct p a b hp (by omega) (by omega) hab
  exact hne (by omega)

theorem paired_product (p : Nat) (hp : Prime p) (xs : List Nat) (hnd : xs.Nodup)
    (hb : ∀ a ∈ xs, 0 < a ∧ a < p)
    (hpairs : ∀ a ∈ xs, ∃ b ∈ xs, b ≠ a ∧ Congruent ((a : Int)*b) 1 p) :
    Congruent (intProduct (xs.map (fun a : Nat => (a : Int)))) 1 p := by
  /-
  Lemma: A distinct list closed under different inverse partners
  has product congruent to one. Proof: Induct on its length.
  The empty product is one. Pair the first entry a with its inverse
  b and remove both. Any remaining entry c still has its partner:
  a removed partner would, by uniqueness of inverses, force c to
  be the other removed entry. Apply induction to the remaining
  list. Rearranging the product puts a*b first, and both this pair
  and the remaining product are congruent to one. QED
  -/
  letI : BEq Nat := instBEqOfDecidableEq
  generalize hk : xs.length = k
  induction k using Nat.strongRecOn generalizing xs with
  | ind k ih =>
    cases xs with
    | nil => simpa [intProduct] using modeq_refl 1 p (by have := hp.1; omega)
    | cons a tail =>
      have hnod := List.nodup_cons.mp hnd
      have ha := hb a (by simp)
      rcases hpairs a (by simp) with ⟨b,hbin,hba,hab⟩
      have hbt : b ∈ tail := (List.mem_cons.mp hbin).resolve_left hba
      let rest := tail.erase b
      have hrest : ∀ c ∈ rest, c ∈ tail := fun c hc => List.mem_of_mem_erase hc
      have hbound : ∀ c ∈ rest, 0 < c ∧ c < p := fun c hc => hb c (by simp [hrest c hc])
      have hremain : ∀ c ∈ rest, ∃ d ∈ rest, d ≠ c ∧ Congruent ((c : Int)*d) 1 p := by
        intro c hc
        have hct := hrest c hc
        have hca : c ≠ a := by intro he; subst c; exact hnod.1 hct
        have hcb : c ≠ b := by
          intro he; subst c
          exact hnod.2.not_mem_erase hc
        rcases hpairs c (by simp [hct]) with ⟨d,hd,hdc,hcd⟩
        have hda : d ≠ a := by
          intro he; subst d
          have hsame := prime_inverse_unique p a c b hp ha.1 ha.2 (hbound c hc).2
            (hb b hbin).2 (by simpa only [Int.mul_comm] using hcd) hab
          exact hcb hsame
        have hdb : d ≠ b := by
          intro he; subst d
          have hsame := prime_inverse_unique p b c a hp (hb b hbin).1 (hb b hbin).2
            (hbound c hc).2 ha.2 (by simpa only [Int.mul_comm] using hcd)
            (by simpa only [Int.mul_comm] using hab)
          exact hca hsame
        have hdt : d ∈ tail := (List.mem_cons.mp hd).resolve_left hda
        exact ⟨d,(List.mem_erase_of_ne hdb).mpr hdt,hdc,hcd⟩
      have hlen : rest.length < k := by
        have he := List.length_erase_of_mem hbt
        simp only [List.length_cons] at hk
        dsimp [rest]; omega
      have hprod := ih rest.length hlen rest (hnod.2.erase b) hbound hremain rfl
      have he := product_perm _ _ ((List.perm_cons_erase hbt).map (fun c : Nat => (c : Int)))
      have hm := modeq_mult _ 1 _ 1 p hab hprod
      change Congruent ((a : Int)*intProduct (tail.map (fun c : Nat => (c : Int)))) 1 p
      rw [he]
      simpa only [List.map_cons,intProduct,Int.mul_assoc,Int.one_mul] using hm

def interiorResidues (p : Nat) : List Nat := ((nonzeroResidues p).erase 1).erase (p-1)

theorem interior_mem (p i : Nat) : i ∈ interiorResidues p ↔ 1 < i ∧ i < p-1 := by
  /-
  Lemma: Removing one and p-1 from the positive representatives
  below p leaves exactly the interior representatives. Proof:
  The original entries satisfy 0<i<p. Distinctness means erasing
  an endpoint excludes it completely. The remaining inequalities
  are precisely 1<i<p-1. QED
  -/
  have hnd : (nonzeroResidues p).Nodup := (List.nodup_range p).erase 0
  unfold interiorResidues
  rw [(hnd.erase 1).mem_erase_iff,hnd.mem_erase_iff,nonzero_residues_mem]
  omega

theorem interior_product (p : Nat) (hp : Prime p) (hp2 : 2 < p) :
    Congruent (intProduct ((interiorResidues p).map (fun i : Nat => (i : Int)))) 1 p := by
  /-
  Theorem: The product of the integers from two through p-2 is
  congruent to one for a prime p>2. Proof: The list is distinct.
  Each entry has a different inverse in the same interval. Pair
  these inverses using the preceding induction on finite lists.
  For p=3 the list is empty and its product is one. QED
  -/
  apply paired_product p hp _ (((List.nodup_range p).erase 0).erase 1 |>.erase (p-1))
  · intro a ha
    have h := (interior_mem p a).mp ha
    omega
  · intro a ha
    have h := (interior_mem p a).mp ha
    rcases interior_inverse_exists p a hp h.1 h.2 with ⟨b,hb,hbp,hba,hab⟩
    exact ⟨b,(interior_mem p b).mpr ⟨hb,hbp⟩,hba,hab⟩

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

theorem factorial_residues (p : Nat) (hp : 0 < p) :
    factorial (p-1)=intProduct ((nonzeroResidues p).map (fun i : Nat => (i : Int))) := by
  /-
  Lemma: The factorial of p-1 is the product of all positive
  representatives below p. Proof: The list 1,...,p-1 has no
  repeats, and its membership condition is exactly 0<i<p.
  It therefore rearranges the nonzero residue list. Products
  are unchanged by a rearrangement. QED
  -/
  have hnd : ((List.range (p-1)).map (fun i => i+1)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp (R := fun i j : Nat => i ≠ j) ?_ (List.nodup_range (p-1))
    intro i j hij he
    exact hij (by omega)
  have hperm : ((List.range (p-1)).map (fun i => i+1)).Perm (nonzeroResidues p) := by
    apply same_members_perm _ _ hnd ((List.nodup_range p).erase 0)
    intro i
    change i ∈ (List.range (p-1)).map (fun j => j+1) ↔ i ∈ nonzeroResidues p
    simp only [List.mem_map,List.mem_range,nonzero_residues_mem]
    constructor
    · rintro ⟨j,hj,he⟩; omega
    · rintro ⟨hi,hip⟩
      exact ⟨i-1,by omega,by omega⟩
  rw [factorial_product]
  exact product_perm _ _ (hperm.map (fun i : Nat => (i : Int)))

theorem factorial_interior (p : Nat) (hp : 2 < p) :
    factorial (p-1)=((p : Int)-1)*intProduct ((interiorResidues p).map (fun i : Nat => (i : Int))) := by
  /-
  Lemma: For p>2, removing the two endpoints from the factorial
  leaves (p-1) times the interior product. Proof: Rearrange the
  positive residue list to place one first, then place p-1 first
  in the remaining list. These are different entries. Removing
  them gives the interior list, and the factor one disappears.
  QED
  -/
  have hnd : (nonzeroResidues p).Nodup := (List.nodup_range p).erase 0
  have hind : (interiorResidues p).Nodup := ((hnd.erase 1).erase (p-1))
  letI : BEq Nat := instBEqOfDecidableEq
  have h1 : 1 ∈ nonzeroResidues p := (nonzero_residues_mem p 1).mpr ⟨by omega,by omega⟩
  have hlast : p-1 ∈ (nonzeroResidues p).erase 1 := by
    apply (List.mem_erase_of_ne (by omega : p-1 ≠ 1)).mpr
    exact (nonzero_residues_mem p (p-1)).mpr ⟨by omega,by omega⟩
  have he1 := product_perm _ _ ((List.perm_cons_erase h1).map (fun i : Nat => (i : Int)))
  have he2 := product_perm _ _ ((List.perm_cons_erase hlast).map (fun i : Nat => (i : Int)))
  rw [factorial_residues p (by omega),he1]
  simp only [List.map_cons,intProduct,Int.natCast_one,Int.one_mul]
  rw [he2]
  have hcast : ((p-1 : Nat) : Int)=(p : Int)-1 := by omega
  simp only [List.map_cons,intProduct,hcast]
  have hr : (((nonzeroResidues p).erase 1).erase (p-1)).Perm (interiorResidues p) := by
    apply same_members_perm _ _ ((hnd.erase 1).erase (p-1))
      hind
    intro i
    change i ∈ ((nonzeroResidues p).erase 1).erase (p-1) ↔ i ∈ interiorResidues p
    rw [(hnd.erase 1).mem_erase_iff,hnd.mem_erase_iff,nonzero_residues_mem,interior_mem]
    omega
  rw [product_perm _ _ (hr.map (fun i : Nat => (i : Int)))]

theorem wilson (p : Nat) (hp : Prime p) : Congruent (factorial (p-1)) (-1) p := by
  /-
  Theorem: For a prime p, the factorial of p-1 is congruent to -1.
  Proof: If p=2, the factorial is one and its difference from -1
  is two. Otherwise the interior factors pair to give one modulo
  p. The endpoints contribute 1*(p-1), which is congruent to -1.
  Multiplying these congruences proves the assertion. QED
  -/
  have hp1 := hp.1
  by_cases he : p=2
  · subst p
    exact ⟨by decide,1,by decide⟩
  · have hp2 : 2 < p := by omega
    rw [factorial_interior p hp2]
    have hend : Congruent ((p : Int)-1) (-1) p := ⟨by omega,1,by omega⟩
    have hm := modeq_mult _ (-1) _ 1 p hend (interior_product p hp hp2)
    simpa only [Int.mul_one] using hm

theorem divides_factorial (d k : Nat) (hd : 0 < d) (hdk : d ≤ k) : (d : Int) ∣ factorial k := by
  /-
  Lemma: A positive integer at most k divides k!. Proof: Induct
  on k. The zero case is excluded by positivity. If d=k+1,
  the recursive factorial exhibits the quotient k!. Otherwise
  d≤k and the inductive divisibility persists after multiplying
  by k+1. QED
  -/
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : d=k+1
    · subst d; exact ⟨factorial k,rfl⟩
    · rcases ih (by omega) with ⟨q,hq⟩
      refine ⟨((k+1 : Nat) : Int)*q,?_⟩
      simp only [factorial,hq]
      rw [← Int.mul_assoc,Int.mul_comm ((k+1 : Nat) : Int) d,Int.mul_assoc]

theorem wilson_converse (n : Nat) (hn : 1 < n)
    (h : Congruent (factorial (n-1)) (-1) n) : Prime n := by
  /-
  Theorem: If n>1 and (n-1)! is congruent to -1 modulo n,
  then n is prime. The hypothesis n>1 is necessary: modulo one
  the congruence holds, but one is not prime.
  Proof: Let d divide n. If d is neither one nor n, positivity
  and the divisor bound give 1<d<n. Thus d divides (n-1)!.
  The congruence says (n-1)!+1=n*q for some integer q.
  Since d divides n as well, it divides n*q-(n-1)!=1.
  A positive divisor of one is at most one, contradicting d>1.
  Hence every divisor is one or n, proving primality. QED
  -/
  refine ⟨hn,?_⟩
  intro d hd
  by_cases hd1 : d=1
  · exact Or.inl hd1
  · by_cases hdn : d=n
    · exact Or.inr hdn
    · have hdpos : 0 < d := by
        by_cases hz : d=0
        · subst d
          rcases hd with ⟨q,hq⟩
          simp only [Nat.zero_mul] at hq
          omega
        · omega
      have hdi : (d : Int) ∣ (n : Int) := Int.ofNat_dvd.mpr hd
      have hbound := divisor_le_positive d n (by omega) hdi
      have hdf := divides_factorial d (n-1) hdpos (by omega)
      rcases h.2 with ⟨q,hq⟩
      have hone := dvd_linear d n (factorial (n-1)) q (-1) hdi hdf
      have he : (n : Int)*q+factorial (n-1)*(-1)=1 := by
        simp only [Int.mul_neg,Int.mul_one]
        omega
      rw [he] at hone
      have hdle := divisor_le_positive d 1 (by decide) hone
      omega

end NumberTheory.ReducedResidues
