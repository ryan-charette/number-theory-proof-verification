import «26_right_triangles»
import «23_square_classes»

namespace NumberTheory.SquarePairs

open NumberTheory.Factorization (Prime)
open NumberTheory.RightTriangles (square_residue_four)

theorem prime_square_remainder (p : Nat) (hp : Prime p) (a b : Int)
    (he : a*a+b*b=(p:Int)) : p=2 ∨ p%4=1 := by
  /-
  Theorem: A prime expressed as a sum of two integer squares is either
  two or has remainder one modulo four.
  Proof: Each square has remainder zero or one modulo four, so their
  sum cannot have remainder three. If the prime is even, two divides
  it and primality forces it to equal two. Otherwise it is odd, and
  the only remaining remainder modulo four is one. QED
  -/
  have ha := square_residue_four a
  have hb := square_residue_four b
  have hm : (a*a+b*b)%4=(p:Int)%4 := congrArg (fun x : Int => x%4) he
  rw [Int.add_emod] at hm
  by_cases htwo : p%2=0
  · have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero htwo
    rcases hp.2 2 hd with h | h
    · omega
    · exact Or.inl h.symm
  · right
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rw [ha,hb] at hm <;> omega

theorem square_pair_product_identity (a b c d : Int) :
    (a*a+b*b)*(c*c+d*d)=(a*c+b*d)*(a*c+b*d)+(b*c-a*d)*(b*c-a*d) := by
  /-
  Theorem: The product of two sums of squares is a sum of squares:
  (a*a+b*b)*(c*c+d*d)=(a*c+b*d)^2+(b*c-a*d)^2.
  Proof: Expand the right side. The two mixed terms 2*a*b*c*d and
  -2*a*b*c*d cancel. The remaining terms are a*a*c*c, a*a*d*d,
  b*b*c*c, and b*b*d*d, exactly the expansion of the left side. QED
  -/
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

end NumberTheory.SquarePairs
