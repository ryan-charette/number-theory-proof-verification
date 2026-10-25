import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «10_modular_solutions»
import «12_modular_powers»
import «13_power_cycles»
import «15_reduced_residues»
import «16_power_recovery»
import «18_order_counts»
import «19_divisor_counts»
import «20_totient_products»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ModularRoots

open NumberTheory (Congruent modeq_mult modeq_pow modeq_refl modeq_symm modeq_trans)
open NumberTheory.ModularPowers (cancel_coprime congruent_coprime coprime_power order order_spec power_add)
open NumberTheory.PowerCycles (combine_coprime_moduli fermat_coprime order_dvd_iff power_multiple_one prime_coprime)
open NumberTheory.PolynomialResidues (bounded_congruent_equal canonicalLabel canonicalLabel_eq_iff canonicalLabel_spec)
open NumberTheory.CommonDivisors (bezout divisor_le_positive gcd)
open NumberTheory.ReducedResidues (euler_power gcd_one_combination phi phi_prime positive_congruent_equal prime_product_divides same_members_perm)
open NumberTheory.PowerRecovery (distinct_primes_coprime positive_inverse_exponents power_mul prime_shifted_power)
open NumberTheory.DivisorCounts (phi_positive primitive_root_exists)
open NumberTheory.TotientProducts (coprime_power_iff coprime_product_iff phi_multiply)
open NumberTheory.Factorization (Prime)
open NumberTheory.OrderCounts (PrimitiveRoot power_root_in_cycle)
open NumberTheory.ModularSolutions (canonical_solution_count)


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

theorem nonzero_roots_count_when_solvable (p k : Nat) (b : Int) (hp : Prime p)
    (hk : 0 < k) (hb : ¬ (p : Int) ∣ b) (hsol : ∃ x : Int, Congruent (x^k) b p) :
    (rootResidues p k b).length=(gcd (k : Int) (p-1 : Nat)).toNat := by
  /-
  Theorem: A solvable positive-power congruence with nonzero
  right-hand side modulo p has gcd(k,p-1) root classes.
  Proof: Choose a primitive root a and write b congruent to a^j.
  Express each nonzero residue as a^(e+1), with 0≤e<p-1. The
  root condition becomes k*e congruent to j-k modulo p-1.
  An existing root gives an exponent solution, so elementary
  linear-congruence counting supplies exactly gcd(k,p-1)
  canonical exponent solutions. Map them to the canonical labels
  of a^(e+1). Distinct exponents have distinct labels. Every such
  label is a root, and every root is coprime and has one of these
  exponents. Thus the root and exponent lists have equal lengths.
  The nonzero hypothesis is essential and is the approved
  correction; the zero class was counted separately. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hd : 0 < p-1 := by have := hp.1; omega
  have hbc := prime_coprime b p hp hb
  rcases primitive_root_exists p hp with ⟨a,_,_,ha⟩
  rcases primitive_index a b p hp ha hbc with ⟨j,_hj,hbj⟩
  have hlinear : ∃ e : Int, Congruent ((k : Int)*e) (((j+1 : Nat) : Int)-k) (p-1 : Nat) := by
    rcases hsol with ⟨x,hx⟩
    have hxc := root_is_coprime x b p k hk hbc hx
    rcases primitive_index a x p hp ha hxc with ⟨e,_,hxe⟩
    have hroot := modeq_trans _ _ _ p (modeq_pow _ _ p k (modeq_symm _ _ p hxe)) hx
    exact ⟨e,(primitive_power_root_iff a b p k e (j+1) hp ha hbj).mp hroot⟩
  rcases canonical_solution_count k (((j+1 : Nat) : Int)-k) (p-1 : Nat) (by omega) hlinear with
    ⟨es,hnd,hlen,hmem⟩
  let label (e : Int) : Nat := canonicalLabel ((a : Int)^(e.toNat+1)) p
  have hlabels : (es.map label).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem ?_ hnd
    intro e f he hf hef heq
    have he' := (hmem e).mp he
    have hf' := (hmem f).mp hf
    have hecast : (e.toNat : Int)=e := Int.toNat_of_nonneg he'.1
    have hfcast : (f.toNat : Int)=f := Int.toNat_of_nonneg hf'.1
    have h := primitive_labels_injective a p e.toNat f.toNat hp ha (by omega) (by omega) heq
    exact hef (by omega)
  have hperm : (es.map label).Perm (rootResidues p k b) := by
    apply same_members_perm _ _ hlabels (root_residues_nodup p k b)
    intro r
    constructor
    · intro hr
      rcases List.mem_map.mp hr with ⟨e,he,her⟩
      subst r
      have he' := (hmem e).mp he
      have hecast : (e.toNat : Int)=e := Int.toNat_of_nonneg he'.1
      have hlin : Congruent ((k : Int)*e.toNat) (((j+1 : Nat) : Int)-k) (p-1 : Nat) := by
        rw [hecast]; exact he'.2.2
      have hroot := (primitive_power_root_iff a b p k e.toNat (j+1) hp ha hbj).mpr hlin
      have hl := canonicalLabel_spec ((a : Int)^(e.toNat+1)) p hn
      apply (root_residues_mem p k (label e) b).mpr
      exact ⟨hl.1,modeq_trans _ _ _ p (modeq_pow _ _ p k (modeq_symm _ _ p hl.2)) hroot⟩
    · intro hr
      have hr' := (root_residues_mem p k r b).mp hr
      have hrc := root_is_coprime r b p k hk hbc hr'.2
      rcases primitive_index a r p hp ha hrc with ⟨e,he,hre⟩
      have hroot := modeq_trans _ _ _ p (modeq_pow _ _ p k (modeq_symm _ _ p hre)) hr'.2
      have hlin := (primitive_power_root_iff a b p k e (j+1) hp ha hbj).mp hroot
      have hemem : (e : Int) ∈ es := (hmem e).mpr ⟨by omega,by omega,hlin⟩
      have hl := canonicalLabel_spec ((a : Int)^(e+1)) p hn
      have heq := bounded_congruent_equal r (canonicalLabel ((a : Int)^(e+1)) p) p
        (by omega) (by omega) (by omega) (by omega) (modeq_trans _ _ _ p hre hl.2)
      refine List.mem_map.mpr ⟨(e : Int),hemem,?_⟩
      change canonicalLabel ((a : Int)^(e+1)) p=r
      omega
  have h := hperm.length_eq
  rw [List.length_map,hlen] at h
  exact h.symm

theorem nonzero_root_count (p k : Nat) (b : Int) (hp : Prime p) (hk : 0 < k)
    (hb : ¬ (p : Int) ∣ b) :
    (rootResidues p k b).length=0 ∨
      (rootResidues p k b).length=(gcd (k : Int) (p-1 : Nat)).toNat := by
  /-
  Theorem: For a nonzero right-hand side modulo a prime, the
  number of positive-power roots is zero or gcd(k,p-1).
  Proof: If the canonical root list is empty, its length is zero.
  Otherwise its first entry provides a solution, and the solvable
  case gives exactly gcd(k,p-1) roots. QED
  -/
  cases he : rootResidues p k b with
  | nil => exact Or.inl rfl
  | cons r rs =>
    have hr : r ∈ rootResidues p k b := by rw [he]; simp
    have h := nonzero_roots_count_when_solvable p k b hp hk hb
      ⟨r,((root_residues_mem p k r b).mp hr).2⟩
    exact Or.inr (by simpa only [he] using h)

theorem prime_root_count (p k : Nat) (b : Int) (hp : Prime p) (hk : 0 < k) :
    ((p : Int) ∣ b ∧ (rootResidues p k b).length=1) ∨
      (¬ (p : Int) ∣ b ∧ ((rootResidues p k b).length=0 ∨
        (rootResidues p k b).length=(gcd (k : Int) (p-1 : Nat)).toNat)) := by
  /-
  Theorem: The corrected root count separates zero from nonzero
  right-hand sides. If p divides b there is exactly one root
  class. Otherwise there are zero or gcd(k,p-1) root classes.
  Proof: Decide whether p divides b and apply the appropriate
  count already proved. This retains all integer right-hand
  sides and makes the necessary zero-residue exception explicit.
  Exponent positivity matches the natural-number convention.
  QED
  -/
  by_cases hb : (p : Int) ∣ b
  · exact Or.inl ⟨hb,zero_root_count p k b hp hk hb⟩
  · exact Or.inr ⟨hb,nonzero_root_count p k b hp hk hb⟩

end NumberTheory.ModularRoots
