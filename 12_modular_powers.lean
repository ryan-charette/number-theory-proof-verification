import «01_divisibility»
import «02_remainders»
import «03_common_divisors»
import «05_divisibility_tests»
import «09_polynomial_residues»
import «11_simultaneous_congruences»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ModularPowers

open NumberTheory.CommonDivisors (bezout divisor_le_positive dvd_linear gcd gcd_data gcd_positive)
open NumberTheory.Remainders (least_natural)
open NumberTheory (Congruent modeq_symm)
open NumberTheory.PolynomialResidues (canonicalLabel canonicalLabel_eq_iff canonicalLabel_spec)
open NumberTheory.DivisibilityTests (distinct_length_bound)
open NumberTheory.SimultaneousCongruences (bezout_product)


theorem gcd_one_right (a n : Int) (hn : 0 < n)
    (h : ∃ u v : Int, a*u+n*v=1) : gcd a n=1 := by
  /-
  Lemma: A positive modulus n and a linear combination a*u+n*v=1
  imply gcd(a,n)=1, even when a is zero or negative.
  Proof: The positive gcd divides this linear combination, so it
  divides one and is at most one. Positivity makes it exactly one.
  QED
  -/
  rcases h with ⟨u,v,he⟩
  have hd := dvd_linear (gcd a n) a n u v
    (gcd_data a n).2.1 (gcd_data a n).2.2.1
  rw [he] at hd
  have hle := divisor_le_positive (gcd a n) 1 (by decide) hd
  have hp := gcd_positive a n (Or.inr (by omega))
  omega

theorem coprime_power (a n : Int) (hn : 0 < n) (hcop : gcd a n=1) (j : Nat) :
    gcd (a^j) n=1 := by
  /-
  Theorem: Every nonnegative power of a number relatively prime
  to n remains relatively prime to n.
  Proof: Bezout gives a*u+n*v=1. We prove by induction that n and
  a^j have a linear combination equal to one. For j=0, a^0=1.
  At the induction step, combine the identities for n with a^j
  and with a to get an identity for n with a^j*a. Reorder its
  terms and use the preceding lemma to identify the gcd as one.
  This proof permits all integer bases, extending the positive-base
  statement, and also includes exponent zero. QED
  -/
  rcases bezout a n with ⟨u,v,he⟩
  rw [hcop] at he
  have hb : ∃ s t : Int, n*s+a*t=1 := ⟨v,u,by omega⟩
  have hp : ∀ k : Nat, ∃ s t : Int, n*s+a^k*t=1 := by
    intro k
    induction k with
    | zero => exact ⟨0,1,by simp [Int.pow_zero]⟩
    | succ k ih =>
      simpa only [Int.pow_succ] using bezout_product n (a^k) a ih hb
  rcases hp j with ⟨s,t,ht⟩
  exact gcd_one_right (a^j) n hn ⟨t,s,by omega⟩

theorem congruent_coprime (a b n : Int) (hcop : gcd a n=1)
    (h : Congruent a b n) : gcd b n=1 := by
  /-
  Theorem: Replacing a number by a congruent integer preserves
  coprimality with the modulus.
  Proof: Write a-b=n*q and a*u+n*v=1. Substitution gives
  b*u+n*(q*u+v)=1. This is a Bezout identity for b and n,
  so their gcd is one. QED
  -/
  rcases bezout a n with ⟨u,v,he⟩
  rw [hcop] at he
  rcases h.2 with ⟨q,hq⟩
  apply gcd_one_right b n h.1
  refine ⟨u,q*u+v,?_⟩
  have ht := congrArg (fun z => z*u) hq
  change (a-b)*u=(n*q)*u at ht
  rw [Int.sub_mul,Int.mul_assoc] at ht
  rw [Int.mul_add]
  omega

theorem cancel_coprime (a b c n : Int) (hcop : gcd c n=1)
    (h : Congruent (a*c) (b*c) n) : Congruent a b n := by
  /-
  Theorem: A factor relatively prime to the modulus can be cancelled
  from a congruence.
  Proof: Write (a-b)*c=n*q and c*u+n*v=1. Multiplying the latter
  identity by a-b and substituting the former gives
  a-b=n*(q*u+(a-b)*v). This witness proves the desired congruence.
  QED
  -/
  rcases bezout c n with ⟨u,v,he⟩
  rw [hcop] at he
  rcases h.2 with ⟨q,hq⟩
  have hd : (a-b)*c=n*q := by rw [Int.sub_mul]; exact hq
  refine ⟨h.1,q*u+(a-b)*v,?_⟩
  calc
    a-b = (a-b)*1 := by rw [Int.mul_one]
    _ = (a-b)*(c*u+n*v) := congrArg (fun z => (a-b)*z) he.symm
    _ = ((a-b)*c)*u+n*((a-b)*v) := by
      rw [Int.mul_add,←Int.mul_assoc,Int.mul_left_comm (a-b) n v]
    _ = n*(q*u+(a-b)*v) := by rw [hd,Int.mul_add,Int.mul_assoc]

theorem repeated_powers (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ i j : Nat, 0 < i ∧ i < j ∧ Congruent (a^i) (a^j) n := by
  /-
  Theorem: Two distinct positive powers of any integer are congruent
  modulo a positive n.
  Proof: Label the n+1 powers a^1 through a^(n+1) by their canonical
  remainders. If no two powers were congruent, all these labels
  would be distinct. They lie in the list 0 through n-1, which
  has only n entries. The elementary bound for distinct lists
  would then give n+1≤n, a contradiction. QED
  -/
  apply Classical.byContradiction
  intro hnot
  let f : Nat → Nat := fun i => canonicalLabel (a^(i+1)) n
  have hinj : ∀ i j : Nat, f i=f j → i=j := by
    intro i j he
    have hc := (canonicalLabel_eq_iff (a^(i+1)) (a^(j+1)) n hn).mp he
    by_cases hij : i < j
    · exact False.elim (hnot ⟨i+1,j+1,by omega,by omega,hc⟩)
    · by_cases hji : j < i
      · exact False.elim (hnot ⟨j+1,i+1,by omega,by omega,
          modeq_symm _ _ n hc⟩)
      · omega
  have hnd : ((List.range (n+1)).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp (R := fun i j : Nat => i ≠ j) ?_ (List.nodup_range _)
    intro i j hij he
    exact hij (hinj i j he)
  have hsub : ∀ r ∈ (List.range (n+1)).map f, r ∈ List.range n := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i,_,he⟩
    subst r
    exact List.mem_range.mpr (canonicalLabel_spec (a^(i+1)) n hn).1
  have hb := distinct_length_bound _ _ hnd hsub
  simp only [List.length_map,List.length_range] at hb
  omega

theorem power_add (a : Int) (i j : Nat) : a^(i+j)=a^i*a^j := by
  /-
  Lemma: Adding exponents multiplies the corresponding powers.
  Proof: Induct on j. At zero the second factor is one. In the
  successor step, the recursive rule for powers appends one factor
  a. Apply the induction hypothesis and reassociate the product.
  QED
  -/
  induction j with
  | zero => simp [Int.pow_zero]
  | succ j ih =>
    rw [Nat.add_succ,Int.pow_succ,ih,Int.pow_succ,Int.mul_assoc]

theorem positive_power_one (a : Int) (n : Nat) (hn : 0 < n)
    (hcop : gcd a n=1) : ∃ k : Nat, 0 < k ∧ Congruent (a^k) 1 n := by
  /-
  Theorem: A number relatively prime to a positive modulus has
  a positive power congruent to one.
  Proof: Choose i<j with a^i congruent to a^j. Reverse this
  congruence and factor a^j=a^(j-i)*a^i. The power a^i is still
  relatively prime to n, so it can be cancelled. This leaves
  a^(j-i) congruent to one, and j-i is positive. QED
  -/
  rcases repeated_powers a n hn with ⟨i,j,_,hij,hc⟩
  have he : a^j=a^(j-i)*a^i := by
    rw [←power_add]
    congr 1
    omega
  have hrev := modeq_symm _ _ n hc
  rw [he] at hrev
  have hcancel : Congruent (a^(j-i)*a^i) (1*a^i) n := by simpa using hrev
  exact ⟨j-i,by omega,cancel_coprime (a^(j-i)) 1 (a^i) n
    (coprime_power a n (by omega) hcop i) hcancel⟩



/- Order is the least positive exponent returning to one. Outside
   the positive, coprime case we use zero solely to make it total. -/

noncomputable def order (a : Int) (n : Nat) : Nat :=
  if h : 0 < n ∧ gcd a n=1 then
    Classical.choose (least_natural (fun k => 0 < k ∧ Congruent (a^k) 1 n)
      (positive_power_one a n h.1 h.2))
  else 0

theorem order_spec (a : Int) (n : Nat) (hn : 0 < n) (hcop : gcd a n=1) :
    0 < order a n ∧ Congruent (a^(order a n)) 1 n ∧
      ∀ k : Nat, 0 < k → Congruent (a^k) 1 n → order a n ≤ k := by
  /-
  Theorem: The order is positive, its power is congruent to one,
  and it is no larger than any other positive exponent with that
  property.
  Proof: The positive-power theorem makes the collection of such
  exponents nonempty. Well-ordering supplies a least member. The
  definition chooses that member, so it belongs to the collection
  and is at most every other member. QED

  Positivity is explicit because Lean's natural numbers include
  zero. No claim about the default value outside these hypotheses
  is needed to define order for the textbook's coprime inputs.
  -/
  have hs := Classical.choose_spec
    (least_natural (fun k => 0 < k ∧ Congruent (a^k) 1 n)
      (positive_power_one a n hn hcop))
  unfold order
  rw [dif_pos ⟨hn,hcop⟩]
  exact ⟨hs.1.1,hs.1.2,fun k hk hc => hs.2 k ⟨hk,hc⟩⟩

end NumberTheory.ModularPowers
