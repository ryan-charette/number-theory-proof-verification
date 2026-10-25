import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «05_divisibility_tests»
import «09_polynomial_residues»
import «11_simultaneous_congruences»
import «12_modular_powers»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PowerCycles

open NumberTheory.CommonDivisors (bezout divisor_le_positive dvd_linear dvd_refl gcd gcd_data gcd_positive)
open NumberTheory (Congruent modeq_mult modeq_refl modeq_symm modeq_trans)
open NumberTheory.PolynomialResidues (bounded_congruent_equal canonicalLabel canonicalLabel_eq_iff canonicalLabel_spec)
open NumberTheory.DivisibilityTests (distinct_length_bound)
open NumberTheory.SimultaneousCongruences (bezout_product product_divides)
open NumberTheory.ModularPowers (cancel_coprime coprime_power gcd_one_right order order_spec power_add)
open NumberTheory.Factorization (Prime)


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

theorem fermat_all (a : Int) (p : Nat) (hp : Prime p) : Congruent (a^p) a p := by
  /-
  Theorem: For every integer a and prime p, a^p is congruent to a.
  Proof: The coprime form has been proved by rearranging residues
  and cancelling their product. The forward implication of the
  equivalence just proved supplies this unrestricted form. QED
  -/
  exact (fermat_forms_equivalent p hp).mp (fun b hb => fermat_coprime b p hp hb) a

theorem order_dvd_prime_predecessor (a : Int) (p : Nat) (hp : Prime p)
    (hc : gcd a p=1) : order a p ∣ p-1 := by
  /-
  Corollary: For a coprime input modulo a prime, the order divides
  p-1. Proof: Fermat's coprime form says this exponent returns to
  one. The exponent-divisibility characterization therefore applies.
  QED
  -/
  exact (order_dvd_iff a p (by have := hp.1; omega) hc (p-1)).mp
    (fermat_coprime a p hp hc)

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

end NumberTheory.PowerCycles
