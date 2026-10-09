import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PolynomialResidues

theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b + c := by
  /-
  Theorem: A common divisor divides the sum.
  Proof: Write b = a * m and c = a * n. Then

    b + c = a * m + a * n    [Substitution]
          = a * (m + n)      [Distributivity]

  The integer m + n is the required witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m + n
  rw [hm, hn, Int.mul_add]

theorem dvd_mult_of_dvd_left (a b c : Int) (h : a ∣ b) : a ∣ b * c := by
  /-
  Theorem: If a divides b, then a divides b * c for any integer c.
  Proof: If b = a * m, then

    b * c = (a * m) * c = a * (m * c).

  Use m * c as the witness. QED
  -/
  rcases h with ⟨m, hm⟩
  exists m * c
  rw [hm, Int.mul_assoc]

def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a-b

local notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

theorem modeq_refl (a n : Int) (hn : 0 < n) : a ≡ a [MOD n] := by
  /-
  Theorem: Every integer is congruent to itself.
  Proof: The modulus n is positive by hypothesis. Also,

    a - a = 0 = n * 0.

  Thus n divides a - a, using the integer 0. QED
  -/
  constructor
  · exact hn
  · exists 0
    rw [Int.sub_self, Int.mul_zero]

theorem modeq_symm (a b n : Int) (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  /-
  Theorem: Reversing a congruence preserves it.
  Proof: By the definition of congruence, n is positive and
  a - b = n * k for some integer k. Then

    b - a = -(a - b) = -(n * k) = n * (-k).

  Use -k as the witness. QED
  -/
  rcases h with ⟨hn, k, hk⟩
  constructor
  · exact hn
  · exists -k
    rw [← Int.neg_sub a b, hk, Int.mul_neg]

theorem modeq_trans (a b c n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  /-
  Theorem: Two consecutive congruences combine.
  Proof: The hypotheses tell us that n divides a - b and b - c.
  Therefore n divides their sum. Adding the differences gives:

    (a - b) + (b - c) = a - c.

  Both differences are divisible by n, so their sum is too. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (b - c) h₀.2 h₁.2
    rw [← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem modeq_add (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  /-
  Theorem: Congruences can be added.
  Proof: We must show that n divides (a + c) - (b + d).
  Rearranging the additions and subtractions gives

    (a + c) - (b + d) = (a - b) + (c - d).

  By hypothesis, n divides each term on the right. Our theorem on
  divisibility of sums shows that n divides the left side as well. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (c - d) h₀.2 h₁.2
    have heq : (a + c) - (b + d) = (a - b) + (c - d) := by
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc]
      rw [Int.add_left_comm c (-b)]
    rw [heq]
    exact h

theorem modeq_mult (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] := by
  /-
  Theorem: Congruences can be multiplied.
  Proof: We must show that n divides a * c - b * d. We can express
  this difference in terms of a - b and c - d:

    a * c - b * d = a * c - b * c + b * c - b * d
                 = (a - b) * c + b * (c - d).

  Since n divides a - b, it divides (a - b) * c. Similarly, since n
  divides c - d, it divides b * (c - d). It therefore divides their
  sum, which is a * c - b * d. QED
  -/
  constructor
  · exact h₀.1
  · have h₂ := dvd_mult_of_dvd_left n (a - b) c h₀.2
    have h₃ := dvd_mult_of_dvd_left n (c - d) b h₁.2
    have h := dvd_add n ((a - b) * c) ((c - d) * b) h₂ h₃
    rw [Int.mul_comm (c - d) b, Int.sub_mul, Int.mul_sub,
      ← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem modeq_pow_step (a b n : Int) (k : Nat)
    (h : a ≡ b [MOD n]) (hk : a ^ k ≡ b ^ k [MOD n]) :
    a ^ (k + 1) ≡ b ^ (k + 1) [MOD n] := by
  /-
  Theorem: Advance an exponent by one.
  Proof: a ^ (k + 1) = a ^ k * a, and likewise for b.
  Multiply the two assumed congruences. QED
  -/
  rw [Int.pow_succ, Int.pow_succ]
  exact modeq_mult (a ^ k) (b ^ k) a b n hk h

theorem modeq_pow (a b n : Int) (k : Nat) (h : a ≡ b [MOD n]) :
    a ^ k ≡ b ^ k [MOD n] := by
  /-
  Theorem: Every natural-number power preserves congruence.
  Proof: We use induction on k, including zero.

  Base case: When k = 0, both powers are 1. We have already shown
  that every integer is congruent to itself.

  Inductive case: Suppose a ^ k is congruent to b ^ k modulo n.
  We also know that a is congruent to b modulo n. Multiplying these
  congruences gives

    a ^ k * a ≡ b ^ k * b [MOD n].

  These products are a ^ (k + 1) and b ^ (k + 1), as required.

  QED
  -/
  induction k with
  | zero =>
    rw [Int.pow_zero, Int.pow_zero]
    exact modeq_refl 1 n h.1
  | succ k ih =>
    exact modeq_pow_step a b n k h ih


def evaluate : List Int → Int → Int
  | [], _ => 0
  | a :: cs, x => a + x * evaluate cs x

theorem polynomial_congruence (cs : List Int) (a b m : Int)
    (h : a ≡ b [MOD m]) : evaluate cs a ≡ evaluate cs b [MOD m] := by
  /-
  Theorem: An integer polynomial takes congruent values at congruent
  integer inputs. Proof: Store coefficients in increasing power order.
  The empty list evaluates to zero. For a first coefficient c and
  remaining polynomial g, the polynomial is c+x*g(x). Induction
  gives g(a) congruent to g(b). Multiply this by the input congruence
  and add c to obtain the desired congruence. QED

  This list representation includes every integer polynomial. The
  proof also covers constant polynomials and leading zero coefficients.
  -/
  induction cs with
  | nil => exact modeq_refl 0 m h.1
  | cons c cs ih =>
    exact modeq_add c c (a*evaluate cs a) (b*evaluate cs b) m
      (modeq_refl c m h.1) (modeq_mult a b (evaluate cs a) (evaluate cs b) m h ih)


theorem congruent_dvd_iff (a b m : Int) (h : a ≡ b [MOD m]) : m ∣ a ↔ m ∣ b := by
  /-
  Lemma: Congruent integers are either both divisible by their modulus
  or neither is. Proof: Write a-b=m*t. If a=m*u, then b=m*(u-t).
  Conversely, if b=m*u, then a=m*(u+t). These are explicit witnesses.
  QED
  -/
  rcases h.2 with ⟨t,ht⟩
  constructor
  · rintro ⟨u,hu⟩
    exists u-t
    rw [Int.mul_sub]
    omega
  · rintro ⟨u,hu⟩
    exists u+t
    rw [Int.mul_add]
    omega


def digitCoefficients (digits : List (Fin 10)) : List Int := digits.map (fun d => (d.val : Int))
def decimalValue (digits : List (Fin 10)) : Int := evaluate (digitCoefficients digits) 10
def digitSum (digits : List (Fin 10)) : Int := evaluate (digitCoefficients digits) 1

theorem nine_dvd_iff_digit_sum (digits : List (Fin 10)) :
    (9 : Int) ∣ decimalValue digits ↔ (9 : Int) ∣ digitSum digits := by
  /-
  Corollary: A decimal number is divisible by nine exactly when the
  sum of its digits is. Proof: Regard its digits, units first, as
  polynomial coefficients. Evaluation at ten gives the number;
  evaluation at one gives the sum of its digits. Since 10-1=9,
  the inputs are congruent modulo nine. Polynomial congruence makes
  the two values congruent, so divisibility by nine is equivalent.
  Leading zero digits and the empty representation are allowed. QED
  -/
  exact congruent_dvd_iff _ _ 9
    (polynomial_congruence (digitCoefficients digits) 10 1 9 ⟨by decide,1,by decide⟩)


theorem three_dvd_iff_digit_sum (digits : List (Fin 10)) :
    (3 : Int) ∣ decimalValue digits ↔ (3 : Int) ∣ digitSum digits := by
  /-
  Corollary: A decimal number is divisible by three exactly when its
  digit sum is. Proof: The digit polynomial evaluated at ten gives
  the number and at one gives the sum. The difference 10-1=3*3
  makes these inputs congruent modulo three. Apply polynomial
  congruence and the divisibility equivalence. QED
  -/
  exact congruent_dvd_iff _ _ 3
    (polynomial_congruence (digitCoefficients digits) 10 1 3 ⟨by decide,3,by decide⟩)

end NumberTheory.PolynomialResidues
