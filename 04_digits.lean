import «03_powers»

/-
A decimal expansion is a list of digits, each between 0 and 9. We put the
units digit first: [1, 3, 1, 1] represents 1131. Removing the units digit
leaves a shorter expansion, which makes induction on the digits natural.
The empty list represents zero; leading zeroes are allowed.
-/

namespace NumberTheory

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
  Proof: We use induction on the list of digits.

  Base case: Both values are zero.
  Inductive case: Let a be the units digit and v the remaining value.
  By the inductive hypothesis v is congruent to the remaining sum s.

    a + 10 * v ≡ a + 1 * s = a + s.

  Multiplication and addition of congruences justify the step. QED
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
  Theorem 1.21: A decimal expansion and its digit sum agree modulo 3.
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
  Theorem 1.22: Divisibility of the value implies divisibility of the sum.
  Proof: Let v be the value and s the sum. We know 3 ∣ v - s, so

    3 ∣ v - (v - s) = s.

  This uses divisibility of differences. QED
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
  Theorem 1.23: Divisibility of the sum implies divisibility of the value.
  Proof: With v and s as above, add the two multiples of 3:

    3 ∣ (v - s) + s = v.

  QED
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
  Unnumbered theorem following 1.21: The decimal digit-sum test for 3.
  Proof: Substitute the given decimal representation, then use the two
  implications just proved. QED
  -/
  rw [hn]
  constructor
  · exact digit_sum_dvd_of_value_dvd digits
  · exact value_dvd_of_digit_sum_dvd digits

theorem nine_dvd_iff_digit_sum (n : Nat) (digits : List (Fin 10))
    (hn : n = decimalValue digits) :
    (9 : Int) ∣ (n : Int) ↔ (9 : Int) ∣ (digitSum digits : Int) := by
  /-
  Exercise 1.24: The same test works for 9.
  Proof: 10 - 1 = 9 * 1, so the value and sum are congruent modulo 9.
  Subtract v - s from v for the forward implication; add it to s for
  the reverse implication. QED
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
