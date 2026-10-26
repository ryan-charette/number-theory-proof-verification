import «05_divisibility_tests»

namespace NumberTheory.RightTriangles

open NumberTheory.CommonDivisors
open NumberTheory.DivisibilityTests (coprime_divisors coprime_right_product)

/-
A triple consists of positive integers satisfying the right-triangle equation.
Primitive means that its three entries have no positive common divisor but one.
All parameters called positive below are explicitly required to exceed zero.
-/
theorem square_residue_four (a : Int) : a*a % 4 = 0 ∨ a*a % 4 = 1 := by
  /-
  Lemma: A square leaves remainder zero or one on division by four.
  Proof: The base has remainder zero, one, two, or three. Squaring
  these four possibilities gives remainders zero, one, zero, one. QED
  -/
  have h : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases h with h | h | h | h <;> rw [Int.mul_emod, h] <;> decide

end NumberTheory.RightTriangles
