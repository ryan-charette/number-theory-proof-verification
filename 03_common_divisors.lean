import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Lean.Elab.Tactic.Omega

/-
We study common divisors and integer linear equations using integer
witnesses, ordinary arithmetic, and the Euclidean reduction. Supporting
results are proved here so that this file can be used independently.
-/

namespace NumberTheory.CommonDivisors

theorem dvd_linear (d a b x y : Int) (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ a * x + b * y := by
  /-
  Theorem: A common divisor divides every integer linear combination.
  Proof: Write a = d * u and b = d * v. Then

    a * x + b * y = d * (u * x + v * y).

  The integer u * x + v * y is the required witness. QED
  -/
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  exists u * x + v * y
  rw [hu, hv, Int.mul_add, Int.mul_assoc, Int.mul_assoc]

end NumberTheory.CommonDivisors
