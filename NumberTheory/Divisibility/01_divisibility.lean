import Init.Data.Int.Lemmas
import Init.Data.Int.Pow

namespace NumberTheory

/-
We work with integers and their ordinary arithmetic laws.

Definition: a divides b, written a ∣ b, means that b = a * k for some
integer k. To prove a ∣ b, we must find such an integer and check the
multiplication. The integer k is sometimes called a witness.

In Lean, `rcases h with ⟨k, hk⟩` gives a name k to the integer whose
existence is asserted by h, and a name hk to the equality b = a * k.
The command `exists k` supplies the integer in a divisibility proof.
The command `rw [hk]` substitutes the equality into the goal.
-/


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

theorem dvd_sub (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b - c := by
  /-
  Theorem: A common divisor divides the difference.
  Proof: Write b = a * m and c = a * n. Then

    b - c = a * m - a * n    [Substitution]
          = a * (m - n)      [Distributivity]

  Use m - n as the witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m - n
  rw [hm, hn, Int.mul_sub]

theorem dvd_mult (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b * c := by
  /-
  Theorem: A common divisor divides the product.
  Proof: If b = a * m and c = a * n, then

    b * c = (a * m) * (a * n)    [Substitution]
          = a * (m * (a * n))    [Associativity]

  Use m * (a * n) as the witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m * (a * n)
  rw [hm, hn, Int.mul_assoc]

theorem dvd_mult_sq (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) :
    a ^ 2 ∣ b * c := by
  /-
  Theorem: If a divides both b and c, then a ^ 2 divides b * c.
  Proof: Write b = a * m and c = a * n. Rearranging the factors gives

    b * c = (a * a) * (m * n) = a ^ 2 * (m * n).

  Use m * n as the witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m * n
  rw [hm, hn, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  rw [Int.mul_assoc, ← Int.mul_assoc m a n, Int.mul_comm m a]
  rw [Int.mul_assoc, Int.mul_assoc]

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

theorem dvd_trans (a b c : Int) (h₀ : a ∣ b) (h₁ : b ∣ c) : a ∣ c := by
  /-
  Theorem: If a divides b and b divides c, then a divides c.
  Proof: Write b = a * m and c = b * n. Then

    c = (a * m) * n = a * (m * n).

  Use m * n as the witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m * n
  rw [hn, hm, Int.mul_assoc]

/-
Definition: For a positive integer n, a and b are congruent modulo n
when n divides a - b. We write this as a ≡ b [MOD n].

The Lean definition records two facts together: n > 0 and n ∣ a - b.
If h is a congruence, h.1 gives the first fact and h.2 gives the second.
To prove a congruence, `constructor` asks us to prove these two facts.
All the arguments below use this definition and the divisibility results
already proved above.
-/


def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a - b

notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

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

theorem modeq_sub (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a - c ≡ b - d [MOD n] := by
  /-
  Theorem: Congruences can be subtracted.
  Proof: We must show that n divides (a - c) - (b - d).
  Rearranging the additions and subtractions gives

    (a - c) - (b - d) = (a - b) - (c - d).

  By hypothesis, n divides a - b and c - d. Our theorem on
  divisibility of differences now gives the required result. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_sub n (a - b) (c - d) h₀.2 h₁.2
    have heq : (a - c) - (b - d) = (a - b) - (c - d) := by
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg, Int.add_assoc]
      rw [Int.add_left_comm (-c) (-b)]
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

theorem modeq_square (a b n : Int) (h : a ≡ b [MOD n]) :
    a ^ 2 ≡ b ^ 2 [MOD n] := by
  /-
  Theorem: Squaring preserves congruence.
  Proof: Multiply the given congruence by itself. QED
  -/
  have h₂ := modeq_mult a b a b n h h
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul,
    Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  exact h₂

theorem modeq_cube (a b n : Int) (h : a ≡ b [MOD n]) :
    a ^ 3 ≡ b ^ 3 [MOD n] := by
  /-
  Theorem: Cubing preserves congruence.
  Proof: Multiply the congruence of the squares by the original one. QED
  -/
  rw [Int.pow_succ, Int.pow_succ b]
  exact modeq_mult (a ^ 2) (b ^ 2) a b n (modeq_square a b n h) h

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

/-
A decimal expansion is a finite list of digits, each between 0 and 9.
We store the units digit first. If a is the units digit and v is the value
of the remaining digits, the whole number has value a + 10 * v.
Its digit sum is a plus the sum of the remaining digits.

In Lean, `Fin 10` represents a natural number less than 10, and `a.val`
is that number. `List (Fin 10)` is a finite list of such digits.
The notation `[]` means an empty list, and `a :: digits` means a list
whose first digit is a and whose remaining digits are `digits`.
Both the value and the sum of an empty list are zero. Leading zeroes
are allowed. These conventions let us prove the result by starting with
no digits and adding one digit at a time.
-/


def decimalValue : List (Fin 10) → Nat
  | [] => 0
  | a :: digits => a.val + 10 * decimalValue digits

def digitSum : List (Fin 10) → Nat
  | [] => 0
  | a :: digits => a.val + digitSum digits

theorem decimal_modeq_sum (digits : List (Fin 10)) (n : Int)
    (h : (10 : Int) ≡ 1 [MOD n]) :
    (decimalValue digits : Int) ≡ (digitSum digits : Int) [MOD n] := by
  /-
  Lemma: When 10 is congruent to 1, a decimal expansion is congruent
  to its digit sum.
  Proof: We use induction, adding one digit at a time. All the
  congruences in this proof are modulo n.

  Base case: With no digits, the value and digit sum are both zero,
  so they are congruent.

  Inductive case: Assume the remaining digits have value v and sum s,
  and that v is congruent to s. Let a be the new units digit.
  Since 10 is congruent to 1, multiplication of congruences gives

    10 * v ≡ 1 * s = s.

  Adding a to both sides gives

    a + 10 * v ≡ a + s.

  The left side is the value of the new list of digits, and the right
  side is its digit sum. This proves the induction step. QED
  -/
  induction digits with
  | nil =>
    exact modeq_refl 0 n h.1
  | cons a digits ih =>
    have hm := modeq_mult 10 1 (decimalValue digits) (digitSum digits) n h ih
    rw [Int.one_mul] at hm
    exact modeq_add a.val a.val (10 * (decimalValue digits : Int))
      (digitSum digits) n (modeq_refl a.val n h.1) hm

theorem decimal_modeq_sum_three (digits : List (Fin 10)) :
    (decimalValue digits : Int) ≡ (digitSum digits : Int) [MOD 3] := by
  /-
  Theorem: A decimal expansion and its digit sum agree modulo 3.
  Proof: 10 - 1 = 9 = 3 * 3. Apply the preceding induction. QED
  -/
  apply decimal_modeq_sum digits 3
  constructor
  · decide
  · exists 3

theorem digit_sum_dvd_of_value_dvd (digits : List (Fin 10))
    (h : (3 : Int) ∣ (decimalValue digits : Int)) :
    (3 : Int) ∣ (digitSum digits : Int) := by
  /-
  Theorem: Divisibility of the value implies divisibility of the sum.
  Proof: Let v be the value and s its digit sum. The preceding
  congruence tells us that 3 divides v - s. By hypothesis, 3 also
  divides v. It therefore divides the difference v - (v - s).
  This difference is s, so 3 divides the digit sum. QED
  -/
  have hc := (decimal_modeq_sum_three digits).2
  have hs := dvd_sub 3 (decimalValue digits)
    ((decimalValue digits : Int) - (digitSum digits : Int)) h hc
  rw [Int.sub_sub_self] at hs
  exact hs

theorem value_dvd_of_digit_sum_dvd (digits : List (Fin 10))
    (h : (3 : Int) ∣ (digitSum digits : Int)) :
    (3 : Int) ∣ (decimalValue digits : Int) := by
  /-
  Theorem: Divisibility of the sum implies divisibility of the value.
  Proof: Let v be the value and s its digit sum. We know that 3
  divides v - s, and the hypothesis says that 3 divides s. Hence 3
  divides their sum (v - s) + s, which equals v. QED
  -/
  have hc := (decimal_modeq_sum_three digits).2
  have hv := dvd_add 3 ((decimalValue digits : Int) - (digitSum digits : Int))
    (digitSum digits) hc h
  rw [Int.sub_add_cancel] at hv
  exact hv

theorem three_dvd_iff_digit_sum (n : Nat) (digits : List (Fin 10))
    (hn : n = decimalValue digits) :
    (3 : Int) ∣ (n : Int) ↔ (3 : Int) ∣ (digitSum digits : Int) := by
  /-
  Theorem: The decimal digit-sum test for 3.
  Proof: An "if and only if" statement requires two implications.
  After expressing n by its given digits, the forward implication is
  the theorem that divisibility of the value implies divisibility of
  the sum. The reverse implication is the theorem just proved. QED
  -/
  rw [hn]
  constructor
  · exact digit_sum_dvd_of_value_dvd digits
  · exact value_dvd_of_digit_sum_dvd digits

theorem nine_dvd_iff_digit_sum (n : Nat) (digits : List (Fin 10))
    (hn : n = decimalValue digits) :
    (9 : Int) ∣ (n : Int) ↔ (9 : Int) ∣ (digitSum digits : Int) := by
  /-
  Theorem: A decimal number is divisible by 9 if and only if its
  digit sum is divisible by 9.
  Proof: Since 10 - 1 = 9 * 1, we have 10 ≡ 1 [MOD 9]. Our induction
  on digits shows that the number v and its digit sum s are congruent
  modulo 9. Thus 9 divides v - s.

  Forward implication: Suppose 9 divides v. Then it divides
  v - (v - s) = s.

  Reverse implication: Suppose 9 divides s. Then it divides
  (v - s) + s = v.

  Both implications hold, proving the equivalence. QED
  -/
  have hten : (10 : Int) ≡ 1 [MOD 9] := by
    constructor
    · decide
    · exists 1
  have hc := (decimal_modeq_sum digits 9 hten).2
  rw [hn]
  constructor
  · intro hv
    have hs := dvd_sub 9 (decimalValue digits)
      ((decimalValue digits : Int) - (digitSum digits : Int)) hv hc
    rw [Int.sub_sub_self] at hs
    exact hs
  · intro hs
    have hv := dvd_add 9 ((decimalValue digits : Int) - (digitSum digits : Int))
      (digitSum digits) hc hs
    rw [Int.sub_add_cancel] at hv
    exact hv

end NumberTheory
