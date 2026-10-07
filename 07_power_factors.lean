import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.Int.Pow
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PowerFactors


def geometricSum (x : Int) : Nat → Int
  | 0 => 0
  | m+1 => x * geometricSum x m + 1

theorem geometric_identity (x : Int) (m : Nat) :
    (x-1) * geometricSum x m = x^m-1 := by
  /-
  Lemma: Multiplying 1+x+...+x^(m-1) by x-1 gives x^m-1.
  Proof: For m=0 the sum is empty and both sides are zero. If S
  is the sum for m, the next sum is x*S+1. Then
  (x-1)*(x*S+1) = x*((x-1)*S)+(x-1)
                  = x*(x^m-1)+(x-1) = x^(m+1)-1.
  Induction proves the identity. It supplies the quotient obtained
  by dividing x^m-1 by x-1, without polynomial machinery. QED
  -/
  induction m with
  | zero => rw [geometricSum, Int.pow_zero, Int.mul_zero]; decide
  | succ m ih =>
    rw [geometricSum]
    calc
      (x-1)*(x*geometricSum x m+1)
          = x*((x-1)*geometricSum x m)+(x-1) := by
              simp only [Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_one,
                Int.one_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = x*(x^m-1)+(x-1) := by rw [ih]
      _ = x^(m+1)-1 := by
        rw [Int.pow_succ]
        simp only [Int.mul_sub, Int.mul_one, Int.mul_comm]
        omega


end NumberTheory.PowerFactors
