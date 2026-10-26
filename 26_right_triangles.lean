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

def Triple (a b c : Int) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ a*a + b*b = c*c

theorem even_leg (a b c : Int) (h : Triple a b c) : a % 2 = 0 ∨ b % 2 = 0 := by
  /-
  Theorem: At least one leg of a right triangle with integer sides is even.
  Proof: If both legs were odd, each square would leave remainder one
  modulo four. Their sum would leave remainder two, whereas the square
  of the hypotenuse leaves remainder zero or one. QED
  -/
  have hc := square_residue_four c
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have hb : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  have he := congrArg (fun x : Int => x % 4) h.2.2.2
  change (a*a+b*b)%4=(c*c)%4 at he
  rw [Int.add_emod, Int.mul_emod a, Int.mul_emod b] at he
  rcases ha with ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb <;> simp only [ha, hb] at he <;> omega

theorem scale_triple (a b c d : Int) (h : Triple a b c) (hd : 0 < d) :
    Triple (d*a) (d*b) (d*c) := by
  /-
  Theorem: Multiplying every side by a positive integer gives another triple.
  Proof: The new sides are positive. Multiply the original equation by
  d*d and distribute; its terms are precisely the three new squares. QED
  -/
  refine ⟨Int.mul_pos hd h.1, Int.mul_pos hd h.2.1, Int.mul_pos hd h.2.2.1, ?_⟩
  have he := congrArg (fun x => d*d*x) h.2.2.2
  simpa only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using he

end NumberTheory.RightTriangles
