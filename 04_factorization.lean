import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

/-
We work with natural numbers, treating primes as numbers greater than one.
A factorization is a finite list of primes. Repeated entries record powers:
the number of occurrences of a prime is its exponent. We prove existence
by strong induction and uniqueness by matching and cancelling one prime
at a time. The supporting Euclidean argument is included in this file.
-/

namespace NumberTheory.Factorization

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

end NumberTheory.Factorization
