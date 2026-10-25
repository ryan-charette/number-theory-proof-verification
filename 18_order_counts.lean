import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «05_divisibility_tests»
import «09_polynomial_residues»
import «12_modular_powers»
import «13_power_cycles»
import «15_reduced_residues»
import «16_power_recovery»
import «17_polynomial_roots»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.OrderCounts

open NumberTheory.CommonDivisors (divisor_le_positive gcd gcd_data gcd_positive)
open NumberTheory (Congruent modeq_pow modeq_symm modeq_trans)
open NumberTheory.ModularPowers (cancel_coprime coprime_power order order_spec)
open NumberTheory.DivisibilityTests (distinct_length_bound)
open NumberTheory.PowerCycles (coprime_not_zero fermat_coprime order_dvd_iff power_multiple_one powers_distinct prime_coprime)
open NumberTheory.Factorization (Prime)
open NumberTheory.PolynomialResidues (evaluate leading)
open NumberTheory.PolynomialRoots (root_count)
open NumberTheory.ReducedResidues (phi reducedResidues reduced_mem)
open NumberTheory.PowerRecovery (power_mul)


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

theorem coprime_exponent_order (a : Int) (n i : Nat) (hn : 0 < n)
    (ha : gcd a n=1) (hi : gcd (i : Int) (order a n)=1) : order (a^i) n=order a n := by
  /-
  Theorem: A power a^i has the same order as a when i is coprime
  to that order. Proof: Write d=ord(a) and e=ord(a^i). Since
  (a^i)^e=a^(i*e) is one, d divides i*e. Coprime cancellation
  gives d dividing e, hence d≤e. Conversely (a^i)^d is one,
  since its exponent i*d is a multiple of d. Minimality gives
  e≤d. The two orders are equal. The argument holds for any
  positive modulus, and in particular for a prime modulus. QED
  -/
  have hp := coprime_power a n (by omega) ha i
  have hs := order_spec a n hn ha
  have ht := order_spec (a^i) n hn hp
  have hm : Congruent (a^(i*order (a^i) n)) 1 n := by rw [← power_mul]; exact ht.2.1
  have hd := (order_dvd_iff a n hn ha _).mp hm
  have hcancel : Congruent ((order (a^i) n : Int)*i) (0*i) (order a n) := by
    refine ⟨by omega,?_⟩
    have hdi := Int.ofNat_dvd.mpr hd
    simpa only [Int.natCast_mul,Int.zero_mul,Int.sub_zero,Int.mul_comm] using hdi
  have hc := cancel_coprime (order (a^i) n) 0 i (order a n) hi hcancel
  have hde : order a n ∣ order (a^i) n := Int.ofNat_dvd.mp (by simpa using hc.2)
  have hle := Nat.le_of_dvd ht.1 hde
  have hreturn := power_multiple_one a n (order a n) i hs.2.1
  have hret : Congruent ((a^i)^(order a n)) 1 n := by
    rw [power_mul,Nat.mul_comm i (order a n)]
    exact hreturn
  have hge := ht.2.2 _ hs.1 hret
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

def monomial : Nat → List Int
  | 0 => [1]
  | k+1 => 0 :: monomial k

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

theorem monomial_length (k : Nat) : (monomial k).length=k+1 := by
  /-
  Lemma: The coefficient list for x^k has length k+1.
  Proof: It starts with one coefficient. Each recursive step
  adds one zero to the front, increasing the length by one. QED
  -/
  induction k with
  | zero => rfl
  | succ k ih => simp only [monomial,List.length_cons,ih]

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

theorem equal_order_index (a b : Int) (p : Nat) (hp : Prime p)
    (ha : gcd a p=1) (hb : gcd b p=1) (he : order b p=order a p) :
    ∃ i : Nat, 0 < i ∧ i ≤ order a p ∧ gcd (i : Int) (order a p)=1 ∧ Congruent b (a^i) p := by
  /-
  Lemma: Every element with the same order d as a is represented
  by a power a^i with 1≤i≤d and gcd(i,d)=1. Proof: Its d-th
  power is one, so the full cycle exhausts the possible roots
  and supplies i. Congruence preserves order, so a^i has order d.
  The preceding necessity argument makes i coprime to d. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hroot : Congruent (b^(order a p)) 1 p := by
    rw [← he]
    exact (order_spec b p hn hb).2.1
  rcases power_root_in_cycle a b p hp ha hroot with ⟨i,hi,hid,hbi⟩
  have horder := congruent_orders b (a^i) p hn hb (coprime_power a p (by omega) ha i) hbi
  have hcop := equal_power_order_coprime a p i hn ha (horder.symm.trans he)
  exact ⟨i,hi,hid,hcop,hbi⟩

theorem order_count (p d : Nat) (hp : Prime p) (xs : List Int)
    (hpair : xs.Pairwise (fun a b => ¬ Congruent a b p))
    (horders : ∀ a ∈ xs, gcd a p=1 ∧ order a p=d) : xs.length ≤ phi d := by
  /-
  Theorem: At most phi(d) incongruent integers have order d modulo
  a prime. Proof: If the list is empty, there is nothing to count.
  Otherwise fix its first element a. Each element b is congruent
  to a^i for some 1≤i≤d coprime to d. Choose such an exponent
  for each b. Two elements assigned the same exponent would be
  congruent, which is excluded. Thus the chosen exponents form a
  distinct list drawn from the reduced representatives counted
  by phi(d). The elementary distinct-list bound gives the result.
  Coprimality makes the order meaningful; d=0 consequently admits
  no such elements, and is harmless in this formulation. QED
  -/
  cases xs with
  | nil => exact Nat.zero_le _
  | cons a xs =>
    have ha := horders a (by simp)
    have hspec : ∀ b ∈ a::xs, ∃ i : Nat, 0 < i ∧ i ≤ d ∧ gcd (i : Int) d=1 ∧ Congruent b (a^i) p := by
      intro b hb
      have hs := horders b hb
      have he := equal_order_index a b p hp ha.1 hs.1 (hs.2.trans ha.2.symm)
      simpa only [ha.2] using he
    let index (b : Int) : Nat := if h : b ∈ a::xs then Classical.choose (hspec b h) else 0
    have hindex : ∀ b (_hb : b ∈ a::xs),
        0 < index b ∧ index b ≤ d ∧ gcd (index b : Int) d=1 ∧ Congruent b (a^(index b)) p := by
      intro b hb
      dsimp only [index]
      rw [dif_pos hb]
      exact Classical.choose_spec (hspec b hb)
    have hnd : ((a::xs).map index).Nodup := by
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp_of_mem ?_ hpair
      intro b c hb hc hbc he
      have hs := (hindex b hb).2.2.2
      have ht := (hindex c hc).2.2.2
      rw [he] at hs
      exact hbc (modeq_trans _ _ _ p hs (modeq_symm _ _ p ht))
    have hsub : ∀ i ∈ (a::xs).map index, i ∈ reducedResidues d := by
      intro i hi
      rcases List.mem_map.mp hi with ⟨b,hb,he⟩
      subst i
      have hs := hindex b hb
      exact (reduced_mem d _).mpr ⟨hs.1,hs.2.1,hs.2.2.1⟩
    have hb := distinct_length_bound _ _ hnd hsub
    change (a::xs).length ≤ (reducedResidues d).length
    simpa only [List.length_map] using hb

def PrimitiveRoot (a : Int) (p : Nat) : Prop := gcd a p=1 ∧ order a p=p-1

theorem primitive_residues (a : Int) (p : Nat) (hp : Prime p) (ha : PrimitiveRoot a p) :
    (0::cyclePowers a (p-1)).Pairwise (fun r s => ¬ Congruent r s p) ∧
      ∀ x : Int, ∃ r ∈ 0::cyclePowers a (p-1), Congruent x r p := by
  /-
  Theorem: Zero together with a,a^2,...,a^(p-1) forms a complete
  residue system when a is a primitive root modulo p.
  Proof: The powers are pairwise incongruent because the order
  is p-1. Every power is coprime to p, so none is congruent to
  zero. For any integer x, if p divides x, use the representative
  zero. Otherwise Fermat's theorem gives x^(p-1) congruent to one.
  The full cycle of a exhausts these roots, so x is congruent to
  one of its powers. This proves both distinctness and coverage.

  Primitive-root existence is deliberately deferred to the later
  counting argument, following the textbook's proof order. Nothing
  in this theorem assumes that such a root has been constructed.
  QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hpair := cycle_distinct a p hn ha.1
  rw [ha.2] at hpair
  constructor
  · apply List.pairwise_cons.mpr
    refine ⟨?_,hpair⟩
    intro x hx hz
    rcases List.mem_map.mp hx with ⟨i,_,he⟩
    subst x
    have hcop := coprime_power a p (by omega) ha.1 (i+1)
    exact coprime_not_zero (a^(i+1)) p hp.1 hcop (modeq_symm _ _ p hz)
  · intro x
    by_cases hx : (p : Int) ∣ x
    · exact ⟨0,by simp,⟨by omega,by simpa only [Int.sub_zero] using hx⟩⟩
    · have hcop := prime_coprime x p hp hx
      have hroot := fermat_coprime x p hp hcop
      rw [← ha.2] at hroot
      rcases power_root_in_cycle a x p hp ha.1 hroot with ⟨i,hi,hip,hxi⟩
      refine ⟨a^i,?_,hxi⟩
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨i-1,?_,?_⟩
      · apply List.mem_range.mpr
        rw [ha.2] at hip
        omega
      · congr 1
        omega

end NumberTheory.OrderCounts
