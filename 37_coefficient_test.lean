import «14_binomial_powers»
import Mathlib.Tactic.Ring

namespace NumberTheory.CoefficientTest

open NumberTheory.BinomialPowers NumberTheory.Factorization
open NumberTheory.CommonDivisors NumberTheory.ModularPowers

theorem weighted_coefficient (m j : Nat) (hj : j≤m) :
    ((j+1:Nat):Int)*coefficient (m+1) (j+1) =
    ((m+1:Nat):Int)*coefficient m j := by
  /-
  Multiply both sides by j! (m-j)!. On the left, (j+1)j! is
  (j+1)!, so the factorial formula gives (m+1)!. On the right,
  the same formula gives (m+1)m!, also (m+1)!. The factor we
  introduced is positive, so cancellation proves the identity. QED
  -/
  have hleft := coefficient_factorial (m+1) (j+1) (by omega)
  rw [show m+1-(j+1)=m-j by omega] at hleft
  have hright := coefficient_factorial m j hj
  apply Int.eq_of_mul_eq_mul_left (ne_of_gt (Int.mul_pos (factorial_positive j)
    (factorial_positive (m-j))))
  calc
    _ = coefficient (m+1) (j+1)*(((j+1:Nat):Int)*factorial j)*factorial (m-j) := by ring
    _ = ((m+1:Nat):Int)*factorial m := hleft
    _ = _ := by rw [← hright]; ring

end NumberTheory.CoefficientTest
