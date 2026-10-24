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

theorem dvd_zero (a : Int) : a ∣ 0 := by
  /-
  Theorem: Every integer divides zero.
  Proof: 0 = a * 0, so choose the integer 0. QED
  -/
  exists 0
  rw [Int.mul_zero]

theorem least_natural (P : Nat → Prop) (h : ∃ b, P b) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b := by
  /-
  Theorem: A nonempty collection of natural numbers has a least member.
  Proof: We prove by strong induction on b that if b is a member, the
  collection has a least member. Strong induction allows us to assume
  the assertion for every natural number smaller than b.

  If some member a is smaller than b, the induction hypothesis at a
  gives a least member. If no member is smaller than b, then b itself
  is least. Finally, nonemptiness supplies a member to start with. QED
  -/
  letI := Classical.propDecidable
  have least_below : ∀ b, P b → ∃ a, P a ∧ ∀ c, P c → a ≤ c := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro hb
      by_cases hs : ∃ a, a < b ∧ P a
      · rcases hs with ⟨a, hab, ha⟩
        exact ih a hab ha
      · exists b
        constructor
        · exact hb
        · intro c hc
          apply Nat.le_of_not_lt
          intro hcb
          exact hs ⟨c, hcb, hc⟩
  rcases h with ⟨b, hb⟩
  exact least_below b hb

theorem division_exists (m n : Nat) (hn : 0 < n) :
    ∃ q r : Int, (m : Int) = (n : Int) * q + r ∧ 0 ≤ r ∧ r < (n : Int) := by
  /-
  Theorem: For a natural number m and a positive natural number n,
  there are integers q and r with m = n * q + r and 0 ≤ r < n.
  Lean includes zero among the natural numbers, so we explicitly require
  n > 0. The conclusion also holds when m = 0.

  Proof: Consider all nonnegative integers r for which m = n * q + r
  for some integer q. This collection is nonempty: q = 0 and r = m
  satisfy the equation. Choose its least member r by well-ordering,
  and choose an integer q giving the equation.

  If r ≥ n, then r - n is nonnegative and

    m = n * q + r = n * (q + 1) + (r - n).

  Thus r - n is another member of the collection. Since n > 0,
  it is smaller than r, contradicting the choice of r. Hence r < n.
  The chosen q and r have all the required properties. QED
  -/
  let P : Nat → Prop := fun r => ∃ q : Int, (m : Int) = (n : Int) * q + r
  have hnonempty : ∃ r, P r := by
    exists m
    exists (0 : Int)
    rw [Int.mul_zero, Int.zero_add]
  rcases least_natural P hnonempty with ⟨r, hr, hleast⟩
  rcases hr with ⟨q, hq⟩
  have hsmall : r < n := by
    apply Nat.lt_of_not_ge
    intro hlarge
    have hnext : P (r - n) := by
      exists q + 1
      rw [Int.mul_add, Int.mul_one]
      -- Since n ≤ r, natural subtraction agrees with integer subtraction.
      omega
    have hminimal := hleast (r - n) hnext
    -- Subtracting positive n gives a strictly smaller natural number.
    omega
  exists q, (r : Int)
  exact ⟨hq, by omega, by omega⟩

end NumberTheory.ResidueSigns
