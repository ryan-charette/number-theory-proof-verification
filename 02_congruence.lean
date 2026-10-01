import «01_divisibility»

/-
Congruence means that a positive modulus divides a difference. We include
positivity in the definition, so every use has the textbook's domain.
We use a separate notation rather than a remainder-based library definition.
-/

namespace NumberTheory

def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a - b

notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

theorem modeq_refl (a n : Int) (hn : 0 < n) : a ≡ a [MOD n] := by
  /-
  Theorem 1.9: Every integer is congruent to itself.
  Proof: a - a = 0 = n * 0. Use the witness 0. QED
  -/
  constructor
  · exact hn
  · exists 0
    rw [Int.sub_self, Int.mul_zero]

theorem modeq_symm (a b n : Int) (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  /-
  Theorem 1.10: Reversing a congruence preserves it.
  Proof: If a - b = n * k, then

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
  Theorem 1.11: Two consecutive congruences combine.
  Proof: Adding the differences cancels the middle integer:

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
  Theorem 1.12: Congruences can be added.
  Proof: The new difference is the sum of the old differences:

    (a + c) - (b + d) = (a - b) + (c - d).

  Apply the theorem on divisibility of sums. QED
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
  Theorem 1.13: Congruences can be subtracted.
  Proof: Subtract the two differences:

    (a - c) - (b - d) = (a - b) - (c - d).

  Apply the theorem on divisibility of differences. QED
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
  Theorem 1.14: Congruences can be multiplied.
  Proof: Insert and subtract b * c:

    a * c - b * d = (a - b) * c + b * (c - d).

  Each summand is divisible by n; hence their sum is divisible by n. QED
  -/
  constructor
  · exact h₀.1
  · have h₂ := dvd_mult_of_dvd_left n (a - b) c h₀.2
    have h₃ := dvd_mult_of_dvd_left n (c - d) b h₁.2
    have h := dvd_add n ((a - b) * c) ((c - d) * b) h₂ h₃
    rw [Int.mul_comm (c - d) b, Int.sub_mul, Int.mul_sub,
      ← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

end NumberTheory
