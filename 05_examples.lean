import «04_digits»

/-
These examples check the definitions on concrete integers and connect the
individual results. Closed numerical equalities are checked by `rfl` or
`decide`; the general theorems use explicit witnesses and rewrites.
-/

namespace NumberTheory

-- Exercise 1.7: Test the proposed congruences, including a negative integer.
example : (45 : Int) ≡ 9 [MOD 4] := by
  constructor
  · decide
  · exists 9

example : (37 : Int) ≡ 2 [MOD 5] := by
  constructor
  · decide
  · exists 7

example : ¬ ((37 : Int) ≡ 3 [MOD 5]) := by
  unfold Congruent
  decide

example : (37 : Int) ≡ -3 [MOD 5] := by
  constructor
  · decide
  · exists 8

theorem modeq_iff_multiple (m r n : Int) (hn : 0 < n) :
    m ≡ r [MOD n] ↔ ∃ k : Int, m = r + n * k := by
  /-
  Exercise 1.8: Describe every integer in a congruence class.
  Proof: If m - r = n * k, add r to recover m = r + n * k.
  Conversely, subtracting r from this expression gives n * k. QED
  -/
  constructor
  · intro h
    rcases h.2 with ⟨k, hk⟩
    exists k
    rw [← hk, Int.add_comm, Int.sub_add_cancel]
  · intro h
    rcases h with ⟨k, hk⟩
    constructor
    · exact hn
    · exists k
      rw [hk, Int.add_comm r, Int.add_sub_cancel]

example (m : Int) : m ≡ 0 [MOD 3] ↔ ∃ k : Int, m = 0 + 3 * k := by
  exact modeq_iff_multiple m 0 3 (by decide)

example (m : Int) : m ≡ 1 [MOD 3] ↔ ∃ k : Int, m = 1 + 3 * k := by
  exact modeq_iff_multiple m 1 3 (by decide)

example (m : Int) : m ≡ 2 [MOD 3] ↔ ∃ k : Int, m = 2 + 3 * k := by
  exact modeq_iff_multiple m 2 3 (by decide)

example (m : Int) : m ≡ 3 [MOD 3] ↔ ∃ k : Int, m = 3 + 3 * k := by
  exact modeq_iff_multiple m 3 3 (by decide)

example (m : Int) : m ≡ 4 [MOD 3] ↔ ∃ k : Int, m = 4 + 3 * k := by
  exact modeq_iff_multiple m 4 3 (by decide)

-- Exercise 1.19: Illustrate addition, subtraction, multiplication, and powers.
private theorem seven_modeq_one : (7 : Int) ≡ 1 [MOD 3] := by
  constructor
  · decide
  · exists 2

example : (7 + 7 : Int) ≡ 1 + 1 [MOD 3] := by
  exact modeq_add 7 1 7 1 3 seven_modeq_one seven_modeq_one

example : (7 - 7 : Int) ≡ 1 - 1 [MOD 3] := by
  exact modeq_sub 7 1 7 1 3 seven_modeq_one seven_modeq_one

example : (7 * 7 : Int) ≡ 1 * 1 [MOD 3] := by
  exact modeq_mult 7 1 7 1 3 seven_modeq_one seven_modeq_one

example : (7 : Int) ^ 2 ≡ 1 ^ 2 [MOD 3] := by
  exact modeq_square 7 1 3 seven_modeq_one

example : (7 : Int) ^ 3 ≡ 1 ^ 3 [MOD 3] := by
  exact modeq_cube 7 1 3 seven_modeq_one

example : (7 : Int) ^ (2 + 1) ≡ 1 ^ (2 + 1) [MOD 3] := by
  exact modeq_pow_step 7 1 3 2 seven_modeq_one (modeq_square 7 1 3 seven_modeq_one)

example : (7 : Int) ^ 5 ≡ 1 ^ 5 [MOD 3] := by
  exact modeq_pow 7 1 3 5 seven_modeq_one

theorem cancellation_counterexample :
    (1 * 2 : Int) ≡ 3 * 2 [MOD 4] ∧ ¬ ((1 : Int) ≡ 3 [MOD 4]) := by
  /-
  Question 1.20: A common factor cannot always be cancelled.
  Proof: 2 - 6 = 4 * (-1), but 1 - 3 = -2 is not a multiple of 4.
  Thus even a nonzero common factor can fail to cancel. QED
  -/
  constructor
  · constructor
    · decide
    · exists -1
  · unfold Congruent
    decide

-- The digit-sum theorem applies to a supplied decimal representation.
example : (3 : Int) ∣ 1131 := by
  have hs : (3 : Int) ∣ (digitSum [1, 3, 1, 1] : Int) := by
    exists 2
  exact (three_dvd_iff_digit_sum 1131 [1, 3, 1, 1] (by rfl)).mpr hs

-- Empty and zero-padded expansions also have the intended values.
example : decimalValue [] = 0 := by rfl
example : decimalValue [1, 3, 1, 1, 0] = 1131 := by rfl
example : ¬ ((9 : Int) ∣ 1131) := by
  intro h
  have hs := (nine_dvd_iff_digit_sum 1131 [1, 3, 1, 1] (by rfl)).mp h
  have hnot : ¬ ((9 : Int) ∣ (digitSum [1, 3, 1, 1] : Int)) := by decide
  exact hnot hs

end NumberTheory
