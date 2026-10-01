import Init.Data.Int.Lemmas
import Init.Data.Int.Pow

/-
We work with integers and their ordinary arithmetic laws. The definition
of a ∣ b gives a witness k with b = a * k. Each proof below constructs
such a witness, then checks the equality by substitution and rewriting.
The numbered references refer to Marshall, Odell, and Starbird (2007).
-/

namespace NumberTheory

theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b + c := by
  /-
  Theorem 1.1: A common divisor divides the sum.
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
  Theorem 1.2: A common divisor divides the difference.
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
  Theorem 1.3: A common divisor divides the product.
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
  Question 1.4: The same hypotheses also give divisibility by a squared.
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
  Theorem 1.6 (and the weaker hypothesis in Question 1.4): Only a ∣ b
  is needed to prove divisibility of b * c.
  Proof: If b = a * m, then

    b * c = (a * m) * c = a * (m * c).

  Use m * c as the witness. QED
  -/
  rcases h with ⟨m, hm⟩
  exists m * c
  rw [hm, Int.mul_assoc]

theorem dvd_trans (a b c : Int) (h₀ : a ∣ b) (h₁ : b ∣ c) : a ∣ c := by
  /-
  Question 1.5: One further observation is transitivity of divisibility.
  Proof: Write b = a * m and c = b * n. Then

    c = (a * m) * n = a * (m * n).

  Use m * n as the witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m * n
  rw [hn, hm, Int.mul_assoc]

end NumberTheory
