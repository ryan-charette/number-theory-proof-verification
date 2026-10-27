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

end NumberTheory.SquarePairs
