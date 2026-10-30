import «28_hypotenuses»

namespace NumberTheory.FourthPowers

open NumberTheory.CommonDivisors
open NumberTheory.DivisibilityTests
open NumberTheory.RightTriangles
open NumberTheory.Hypotenuses (coprime_prime_test)
open NumberTheory.Factorization (Prime)

theorem coprime_legs_primitive (a b c : Int) (h : Triple a b c)
    (hc : gcd a b=1) : Primitive a b c := by
  /-
  Lemma: A positive integer right triangle with coprime legs is primitive.
  Proof: A common divisor of its sides divides both legs and hence their
  Bezout combination one. A positive divisor of one is one. QED
  -/
  refine ⟨h,?_⟩
  intro d hd ha hb _
  obtain ⟨u,v,he⟩ := coprime_bezout a b hc
  have hh := dvd_linear d a b u v ha hb
  rw [he] at hh
  have := divisor_le_positive d 1 (by decide) hh
  omega

end NumberTheory.FourthPowers
