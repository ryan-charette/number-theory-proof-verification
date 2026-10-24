import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ResidueSigns

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

def intProduct : List Int → Int
  | [] => 1
  | a::xs => a*intProduct xs

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

theorem dvd_refl (a : Int) : a ∣ a := by
  /-
  Theorem: Every integer divides itself.
  Proof: a = a * 1, so choose the integer 1. QED
  -/
  exists 1
  rw [Int.mul_one]

end NumberTheory.ResidueSigns
