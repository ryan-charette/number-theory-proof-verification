import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «12_modular_powers»
import «13_power_cycles»
import «15_reduced_residues»
import «18_order_counts»
import «23_square_classes»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.DoublePrimes

open NumberTheory (Congruent modeq_pow modeq_refl modeq_symm modeq_trans)
open NumberTheory.PolynomialResidues (bounded_congruent_equal canonical_residue)
open NumberTheory.CommonDivisors (divisor_le_positive)
open NumberTheory.ModularPowers (congruent_coprime coprime_power order order_spec)
open NumberTheory.Factorization (Prime)
open NumberTheory.SquareClasses (SquareClass euler_square_criterion minus_one_square nonsquare_times_nonsquare odd_prime_data square_class_congruent square_one_cases square_times_nonsquare)
open NumberTheory.PowerCycles (coprime_not_zero fermat_coprime order_dvd_iff small_prime_coprime)
open NumberTheory.ReducedResidues (prime_product_divides)
open NumberTheory.OrderCounts (PrimitiveRoot congruent_orders)


theorem square_not_primitive (a : Int) (p : Nat) (hp : Prime p)
    (ho : p%2=1) : ¬ PrimitiveRoot (a^2) p := by
  /-
  Theorem: A square is not a primitive root modulo an odd prime.
  Proof: If it were primitive, it would be coprime to p.
  Euler's criterion would make its half-exponent power one.
  Its order p-1 would then divide the positive smaller integer
  (p-1)/2, which is impossible. Oddness is necessary: modulo
  two, the square one is a primitive root. QED
  -/
  intro hr
  have hn : 0<p := by have := hp.1; omega
  have hh := odd_prime_data p hp ho
  have ha : ¬ (p : Int) ∣ a^2 := by
    intro hd
    exact coprime_not_zero (a^2) p hp.1 hr.1 ⟨by omega,by simpa using hd⟩
  have hs : SquareClass (a^2) p := ⟨a,modeq_refl _ p (by omega)⟩
  have hd := (order_dvd_iff (a^2) p hn hr.1 ((p-1)/2)).mp
    ((euler_square_criterion (a^2) p hp ho ha).mp hs)
  rw [hr.2] at hd
  have := Nat.le_of_dvd hh.1 hd
  omega

theorem double_prime_divisors (q d : Nat) (hq : Prime q) (hd : 0<d)
    (hdiv : d ∣ 2*q) : d=1 ∨ d=2 ∨ d=q ∨ d=2*q := by
  /-
  Lemma: The positive divisors of twice a prime q are among
  1, 2, q, and 2q. Proof: Write dt=2q. The prime q divides
  d or t. Cancel q in that factorization; the remaining
  positive factor divides two, so is one or two. QED
  -/
  rcases hdiv with ⟨t,ht⟩
  have hqt : (q : Int) ∣ (d : Int)*(t : Int) := by
    have h : q ∣ d*t := ⟨2,by omega⟩
    simpa only [Int.natCast_mul] using Int.ofNat_dvd.mpr h
  rcases prime_product_divides q d t hq hqt with hqd | hqt
  · rcases Int.ofNat_dvd.mp hqd with ⟨k,hk⟩
    have hkd : k ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_left (by have := hq.1; omega : 0<q)
      exact ⟨t,by simpa [hk,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using ht⟩
    have hkpos : 0<k := by
      by_cases hz : k=0
      · simp [hz] at hk; omega
      · omega
    have hkle := Nat.le_of_dvd (by decide : 0<2) hkd
    have hcases : k=1 ∨ k=2 := by omega
    rcases hcases with h | h
    · right; right; left; simpa [h] using hk
    · right; right; right; simpa [h,Nat.mul_comm] using hk
  · rcases Int.ofNat_dvd.mp hqt with ⟨k,hk⟩
    have hdd : d ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_left (by have := hq.1; omega : 0<q)
      exact ⟨k,by simpa [hk,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using ht⟩
    have hle := Nat.le_of_dvd (by decide : 0<2) hdd
    omega

theorem double_prime_dichotomy (p q a : Nat) (hp : Prime p) (hq : Prime q)
    (he : p=2*q+1) (ha : 0<a) (hb : a<p-1) :
    SquareClass a p ∨ PrimitiveRoot a p := by
  /-
  Theorem: Below p-1, every positive class for a prime p=2q+1
  with q prime is a square or a primitive root.
  Proof: Its order divides 2q, hence is 1, 2, q, or 2q.
  Orders one and q give a square by Euler's criterion.
  Order two forces the class to be one or minus one; the
  latter is excluded by the bound, and the former is a square.
  Order 2q is precisely the primitive-root case. QED
  -/
  have ho : p%2=1 := by omega
  have hn : 0<p := by omega
  have hc := small_prime_coprime p a hp ha (by omega)
  have hnon : ¬ (p : Int) ∣ (a : Int) := by
    intro h
    exact coprime_not_zero a p hp.1 hc ⟨by omega,by simpa using h⟩
  have hs := order_spec a p hn hc
  have hd := (order_dvd_iff a p hn hc (p-1)).mp (fermat_coprime a p hp hc)
  have hd' : order a p ∣ 2*q := by simpa [he] using hd
  have hh : (p-1)/2=q := by omega
  rcases double_prime_divisors q (order a p) hq hs.1 hd' with h | h | h | h
  · left
    apply (euler_square_criterion a p hp ho hnon).mpr
    apply (order_dvd_iff a p hn hc _).mpr
    rw [h]; exact Nat.one_dvd _
  · have hpow : Congruent ((a : Int)^2) 1 p := by simpa [h] using hs.2.1
    rcases square_one_cases a p hp hpow with h1 | hm
    · left
      exact ⟨1,by simpa using modeq_symm _ _ p h1⟩
    · have hpm : Congruent (a : Int) ((p : Int)-1) p := by
        apply modeq_trans _ (-1) _ p hm
        exact ⟨by omega,⟨-1,by omega⟩⟩
      have hx := bounded_congruent_equal (a : Int) ((p : Int)-1) p
        (by omega) (by omega) (by omega) (by omega) hpm
      omega
  · left
    apply (euler_square_criterion a p hp ho hnon).mpr
    rw [hh,←h]
    exact hs.2.1
  · right
    exact ⟨hc,by omega⟩

theorem double_odd_prime_remainder (p q : Nat) (he : p=2*q+1)
    (hq : q%2=1) : p%4=3 := by
  /-
  Lemma: Twice an odd number plus one is three modulo four.
  Proof: Writing q=2k+1 gives p=4k+3. QED
  -/
  omega

theorem primitive_congruent (a b : Int) (p : Nat) (hp : Prime p)
    (h : Congruent a b p) : PrimitiveRoot a p ↔ PrimitiveRoot b p := by
  /-
  Lemma: Congruent integers have the same primitive-root status.
  Proof: Coprimality is preserved by congruence, and their
  returning powers, hence their least returning exponents,
  coincide. Apply this in both directions. QED
  -/
  have hn : 0<p := by have := hp.1; omega
  constructor
  · intro ha
    have hb := congruent_coprime a b p ha.1 h
    exact ⟨hb,by rw [←congruent_orders a b p hn ha.1 hb h]; exact ha.2⟩
  · intro hb
    have hs := modeq_symm a b p h
    have ha := congruent_coprime b a p hb.1 hs
    exact ⟨ha,by rw [congruent_orders a b p hn ha hb.1 h]; exact hb.2⟩

theorem square_class_not_primitive (a : Int) (p : Nat) (hp : Prime p)
    (ho : p%2=1) (ha : SquareClass a p) : ¬ PrimitiveRoot a p := by
  /-
  Corollary: Every square class fails to be a primitive root
  modulo an odd prime. Proof: Choose its square representative.
  Congruence preserves primitive roots, and a square cannot be
  primitive by the half-exponent argument. QED
  -/
  rcases ha with ⟨x,hx⟩
  intro h
  exact square_not_primitive x p hp ho ((primitive_congruent _ _ p hp hx).mpr h)

theorem negation_square_switch (a : Int) (p : Nat) (hp : Prime p)
    (hm : p%4=3) (ha : ¬ (p : Int) ∣ a) :
    SquareClass a p ↔ ¬ SquareClass (-a) p := by
  /-
  Theorem: Modulo a prime three modulo four, negation exchanges
  nonzero square and nonsquare classes. Proof: Minus one is a
  nonsquare. Its product with a square is a nonsquare; its
  product with a nonsquare is a square. If both a and -a
  were nonsquares, the latter rule applied to -1 and -a
  would make a a square, a contradiction. QED
  -/
  have ho : p%2=1 := by omega
  have hn : ¬ (p : Int) ∣ (-1 : Int) := by
    intro h
    have hd : (p : Int) ∣ 1 := by simpa using Int.dvd_neg.mpr h
    have := divisor_le_positive p 1 (by decide) hd
    have := hp.1
    omega
  have hs : ¬ SquareClass (-1) p := by
    intro h
    have := (minus_one_square p hp ho).mp h
    omega
  constructor
  · intro h
    have ht := square_times_nonsquare a (-1) p hp ho ha hn h hs
    simpa using ht
  · intro h
    apply Classical.byContradiction
    intro hna
    have ht := nonsquare_times_nonsquare a (-1) p hp ho ha hn hna hs
    apply h
    simpa using ht

theorem reflected_square_switch (a p : Nat) (hp : Prime p)
    (hm : p%4=3) (ha : 1<a) (hb : a<p-1) :
    SquareClass a p ↔ ¬ SquareClass (p-a : Nat) p := by
  /-
  Corollary: Reflecting an interior representative a to p-a
  exchanges squares and nonsquares when p is three modulo four.
  Proof: The reflected representative is congruent to -a.
  Use the negation rule and the positive bounds. QED
  -/
  have hc := small_prime_coprime p a hp (by omega) (by omega)
  have hn : ¬ (p : Int) ∣ (a : Int) := by
    intro h
    exact coprime_not_zero a p hp.1 hc ⟨by have := hp.1; omega,by simpa using h⟩
  have he : Congruent (- (a : Int)) ((p-a : Nat) : Int) p := by
    refine ⟨by have := hp.1; omega,⟨-1,?_⟩⟩
    omega
  rw [←square_class_congruent _ _ p he]
  exact negation_square_switch a p hp hm hn

theorem reflected_square_primitive (a p q : Nat) (hp : Prime p) (hq : Prime q)
    (he : p=2*q+1) (ho : q%2=1) (ha : 1<a) (hb : a<p-1) :
    SquareClass a p ↔ PrimitiveRoot (p-a : Nat) p := by
  /-
  Theorem: For p=2q+1 with q an odd prime, an interior
  representative is a square exactly when its reflection
  is primitive. Proof: Negation exchanges squares and
  nonsquares. The reflected representative is still interior,
  so the square-or-primitive dichotomy applies. Its square
  and primitive alternatives cannot overlap. QED
  -/
  have hm := double_odd_prime_remainder p q he ho
  have hs := reflected_square_switch a p hp hm ha hb
  constructor
  · intro h
    rcases double_prime_dichotomy p q (p-a) hp hq he (by omega) (by omega) with h' | h'
    · exact False.elim ((hs.mp h) h')
    · exact h'
  · intro h
    apply hs.mpr
    intro hsquare
    exact square_class_not_primitive _ p hp (by omega) hsquare h

theorem half_squares_distinct (p i j : Nat) (hp : Prime p)
    (hi : 0<i) (hj : 0<j) (hib : 2*i<p) (hjb : 2*j<p) (hne : i≠j) :
    ¬ Congruent ((i : Int)^2) ((j : Int)^2) p := by
  /-
  Theorem: Distinct positive integers below half a prime have
  distinct squares modulo that prime. Proof: Equality of
  squares makes p divide (i-j)(i+j), so p divides a factor.
  The difference has absolute value below p and the sum is
  strictly between zero and p. The first alternative forces
  i=j, and the second is impossible. QED
  -/
  intro h
  have hf : (p : Int) ∣ ((i : Int)-j)*((i : Int)+j) := by
    have he : ((i : Int)-j)*((i : Int)+j)=(i : Int)^2-(j : Int)^2 := by
      simp only [Int.pow_succ,Int.pow_zero,Int.one_mul,Int.mul_one,Int.sub_mul,Int.mul_add,
        Int.mul_sub,Int.mul_comm]
      omega
    rw [he]
    exact h.2
  rcases prime_product_divides p ((i : Int)-j) ((i : Int)+j) hp hf with hd | hs
  · have he := bounded_congruent_equal (i : Int) (j : Int) p
      (by omega) (by omega) (by omega) (by omega) ⟨by have := hp.1; omega,hd⟩
    omega
  · have he := bounded_congruent_equal ((i : Int)+j) 0 p
      (by omega) (by omega) (by decide) (by have := hp.1; omega)
      ⟨by have := hp.1; omega,by simpa using hs⟩
    omega

theorem half_square_representative (a : Int) (p q : Nat) (hp : Prime p)
    (he : p=2*q+1) (ha : ¬ (p : Int) ∣ a) (hs : SquareClass a p) :
    ∃ i : Nat, 1≤i ∧ i≤q ∧ Congruent a ((i : Int)^2) p := by
  /-
  Lemma: Every nonzero square class modulo p=2q+1 has a
  square representative i^2 with 1<=i<=q. Proof: Reduce a
  square root to 0<=r<p. It is nonzero because its square
  is nonzero. If r<=q use r; otherwise use p-r. These have
  the same square modulo p, and one lies in the lower half. QED
  -/
  rcases hs with ⟨x,hx⟩
  have hn : 0<p := Nat.lt_trans (by decide : 0<1) hp.1
  rcases canonical_residue x p hn with ⟨r,hr,hrp,hxr,_⟩
  have has : Congruent a (r^2) p :=
    modeq_trans _ _ _ p (modeq_symm _ _ p hx) (modeq_pow _ _ p 2 hxr)
  have hrpos : 0<r := by
    by_cases hz : r=0
    · apply False.elim
      apply ha
      simpa [hz] using has.2
    · omega
  have hrn : (r.toNat : Int)=r := Int.toNat_of_nonneg hr
  have hcn : (((p : Int)-r).toNat : Int)=(p : Int)-r := Int.toNat_of_nonneg (by omega)
  by_cases hl : r≤q
  · refine ⟨r.toNat,by omega,by omega,?_⟩
    simpa [Int.toNat_of_nonneg hr] using has
  · refine ⟨((p : Int)-r).toNat,by omega,by omega,?_⟩
    have hneg : Congruent r (-((p : Int)-r)) p :=
      ⟨by omega,⟨1,by omega⟩⟩
    have hsq := modeq_pow _ _ p 2 hneg
    have hc : (((p : Int)-r).toNat : Int)=(p : Int)-r :=
      Int.toNat_of_nonneg (by omega)
    rw [hc]
    apply modeq_trans _ (r^2) _ p has
    simpa [Int.pow_succ] using hsq

theorem minus_one_not_primitive (p q : Nat) (hp : Prime p) (hq : Prime q)
    (he : p=2*q+1) : ¬ PrimitiveRoot (-1) p := by
  /-
  Lemma: Minus one is not primitive when p=2q+1 and q is prime.
  Proof: Its square is one, so its order divides two. A
  primitive root would have order 2q, larger than two. QED
  -/
  intro h
  have hn : 0<p := Nat.lt_trans (by decide : 0<1) hp.1
  have hs : Congruent ((-1 : Int)^2) 1 p := by
    exact ⟨by omega,⟨0,by simp⟩⟩
  have hd := (order_dvd_iff (-1) p hn h.1 2).mp hs
  rw [h.2] at hd
  have := Nat.le_of_dvd (by decide : 0<2) hd
  have := hq.1
  omega

theorem double_prime_primitive_criterion (a : Int) (p q : Nat)
    (hp : Prime p) (hq : Prime q) (he : p=2*q+1)
    (ha : ¬ (p : Int) ∣ a) :
    PrimitiveRoot a p ↔ ¬ SquareClass a p ∧ ¬ Congruent a (-1) p := by
  /-
  Theorem: A nonzero class modulo p=2q+1 is primitive exactly
  when it is neither a square nor minus one.
  Proof: Squares and minus one are not primitive. Conversely,
  reduce to a positive representative r<p. If r=p-1 it is
  minus one, excluded here. Otherwise the square-or-primitive
  dichotomy applies and the square alternative is excluded.
  Congruence transfers the resulting primitive root back. QED
  -/
  have hn : 0<p := by omega
  constructor
  · intro h
    constructor
    · intro hs
      exact square_class_not_primitive a p hp (by omega) hs h
    · intro hm
      exact minus_one_not_primitive p q hp hq he ((primitive_congruent a (-1) p hp hm).mp h)
  · rintro ⟨hs,hm⟩
    rcases canonical_residue a p hn with ⟨r,hr,hrp,har,_⟩
    have hrn : (r.toNat : Int)=r := Int.toNat_of_nonneg hr
    have hpos : 0<r := by
      by_cases hz : r=0
      · apply False.elim
        apply ha
        simpa [hz] using har.2
      · omega
    have hlt : r<(p : Int)-1 := by
      by_cases hz : r=(p : Int)-1
      · apply False.elim
        apply hm
        apply modeq_trans _ r _ p har
        exact ⟨by omega,⟨1,by omega⟩⟩
      · omega
    have hc : Congruent a (r.toNat : Int) p := by simpa [hrn] using har
    rcases double_prime_dichotomy p q r.toNat hp hq he (by omega) (by omega) with h | h
    · exact False.elim (hs ((square_class_congruent _ _ p hc).mpr h))
    · exact (primitive_congruent _ _ p hp hc).mpr h

theorem double_prime_nonprimitive_classes (a : Int) (p q : Nat)
    (hp : Prime p) (hq : Prime q) (he : p=2*q+1)
    (ha : ¬ (p : Int) ∣ a) :
    ¬ PrimitiveRoot a p ↔ Congruent a (-1) p ∨
      ∃ i : Nat, 1≤i ∧ i≤q ∧ Congruent a ((i : Int)^2) p := by
  /-
  Theorem: Among nonzero classes modulo p=2q+1, the classes
  that are not primitive are minus one and the squares
  1^2,2^2,...,q^2. Proof: The primitive criterion leaves
  exactly minus one and square classes. Every nonzero square
  has a root in the lower half, giving the displayed list.
  Conversely each listed square and minus one is nonprimitive.
  The statement concerns residue classes: integer representatives
  differing by a multiple of p describe the same class. QED
  -/
  constructor
  · intro h
    by_cases hm : Congruent a (-1) p
    · exact Or.inl hm
    · right
      have hs : SquareClass a p := by
        apply Classical.byContradiction
        intro hs
        exact h ((double_prime_primitive_criterion a p q hp hq he ha).mpr ⟨hs,hm⟩)
      exact half_square_representative a p q hp he ha hs
  · intro h hr
    rcases h with hm | ⟨i,_hi,_hq,hi⟩
    · exact minus_one_not_primitive p q hp hq he ((primitive_congruent _ _ p hp hm).mp hr)
    · exact square_not_primitive i p hp (by omega) ((primitive_congruent _ _ p hp hi).mp hr)

theorem double_prime_primitive_classes (a : Int) (p q : Nat)
    (hp : Prime p) (hq : Prime q) (he : p=2*q+1) (ho : q%2=1)
    (ha : ¬ (p : Int) ∣ a) :
    PrimitiveRoot a p ↔ ∃ i : Nat, 2≤i ∧ i≤q ∧ Congruent a (-((i : Int)^2)) p := by
  /-
  Theorem: For p=2q+1 with q an odd prime, the primitive classes
  are exactly -2^2,-3^2,...,-q^2.
  Proof: A primitive class a is a nonsquare and is not minus
  one. Negation therefore makes -a a square. Choose its lower
  half root i. The value i=1 would give a=-1, so i>=2.
  Conversely i^2 is a nonzero square, so -i^2 is a nonsquare.
  It cannot be minus one: i^2=1 would force i=1 or i=p-1,
  both outside 2<=i<=q. The primitive criterion now applies. QED
  -/
  have hm := double_odd_prime_remainder p q he ho
  have hneg : ¬ (p : Int) ∣ -a := by
    intro h
    exact ha (by simpa using Int.dvd_neg.mpr h)
  constructor
  · intro hr
    have hc := (double_prime_primitive_criterion a p q hp hq he ha).mp hr
    have hs : SquareClass (-a) p :=
      (negation_square_switch (-a) p hp hm hneg).mpr (by simpa using hc.1)
    rcases half_square_representative (-a) p q hp he hneg hs with ⟨i,hi,hib,his⟩
    have hia : Congruent a (-((i : Int)^2)) p := by
      refine ⟨his.1,?_⟩
      have hd := Int.dvd_neg.mpr his.2
      have heq : -(-a-(i : Int)^2)=a-(-((i : Int)^2)) := by omega
      rw [heq] at hd
      exact hd
    have hi2 : 2≤i := by
      by_cases hone : i=1
      · apply False.elim
        apply hc.2
        simpa [hone] using hia
      · omega
    exact ⟨i,hi2,hib,hia⟩
  · rintro ⟨i,hi,hib,hia⟩
    have hc := small_prime_coprime p i hp (by omega) (by omega)
    have hcp := coprime_power i p (by omega) hc 2
    have hnon : ¬ (p : Int) ∣ (i : Int)^2 := by
      intro h
      exact coprime_not_zero _ p hp.1 hcp ⟨by omega,by simpa using h⟩
    have hs : SquareClass ((i : Int)^2) p := ⟨i,modeq_refl _ p (by omega)⟩
    have hns := (negation_square_switch ((i : Int)^2) p hp hm hnon).mp hs
    apply (double_prime_primitive_criterion a p q hp hq he ha).mpr
    constructor
    · intro h
      exact hns ((square_class_congruent _ _ p hia).mp h)
    · intro hminus
      have hsq : Congruent ((i : Int)^2) 1 p := by
        have ht := modeq_trans _ a _ p (modeq_symm _ _ p hia) hminus
        refine ⟨ht.1,?_⟩
        have hd := Int.dvd_neg.mpr ht.2
        have heq : -(-((i : Int)^2)-(-1))=(i : Int)^2-1 := by omega
        rw [heq] at hd
        exact hd
      rcases square_one_cases i p hp hsq with h1 | hm1
      · have hx := bounded_congruent_equal (i : Int) 1 p (by omega)
          (by omega) (by decide) (by omega) h1
        omega
      · have ht : Congruent (i : Int) ((p : Int)-1) p :=
          modeq_trans _ (-1) _ p hm1 ⟨by omega,⟨-1,by omega⟩⟩
        have hx := bounded_congruent_equal (i : Int) ((p : Int)-1) p
          (by omega) (by omega) (by omega) (by omega) ht
        omega

end NumberTheory.DoublePrimes
