import «04_factorization»
import «05_divisibility_tests»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.Int.Pow
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PowerFactors


open NumberTheory.Factorization (Prime nonprime_factors)
open NumberTheory.DivisibilityTests (odd_part_exists)


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

theorem power_sub_one_dvd (x m : Nat) (hx : 0 < x) :
    x-1 ∣ x^m-1 := by
  /-
  Lemma: For positive x, x-1 divides x^m-1.
  Proof: The geometric identity supplies an integer quotient. Both
  the divisor and dividend are nonnegative natural numbers, so integer
  divisibility is equivalent to natural divisibility. Positivity of x
  ensures its powers are at least one, so the natural subtractions
  agree with integer subtraction. QED
  -/
  apply Int.ofNat_dvd.mp
  rw [Int.ofNat_sub (by omega : 1 ≤ x),
    Int.ofNat_sub (by have := Nat.pow_pos (n := m) hx; omega), Int.natCast_pow]
  exact ⟨geometricSum (x : Int) m, (geometric_identity (x : Int) m).symm⟩

theorem prime_exponent_of_two_pow_sub_one (n : Nat) (hp : Prime (2^n-1)) :
    Prime n := by
  /-
  Theorem: If 2^n-1 is prime, n is prime.
  Proof: Exponents zero and one give zero and one, not primes, so
  n>1. If n were not prime, write n=a*b with 1<a<n and 1<b<n.
  The geometric identity makes 2^a-1 a divisor of (2^a)^b-1=2^n-1.
  Since a>1, this divisor exceeds one. Since a<n, it is smaller than
  2^n-1. Both possibilities allowed for a divisor of a prime are
  therefore excluded. This contradiction proves that n is prime. QED
  -/
  have hn : 1 < n := by
    by_cases hz : n = 0
    · subst n; have := hp.1; simp at this
    · by_cases ho : n = 1
      · subst n; have := hp.1; simp at this
      · omega
  by_cases hprime : Prime n
  · exact hprime
  · rcases nonprime_factors n hn hprime with ⟨a,b,ha,han,_,_,he⟩
    have hd := power_sub_one_dvd (2^a) b (Nat.pow_pos (by decide))
    rw [← Nat.pow_mul, ← he] at hd
    have hlarge := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) ha
    have hsmall := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) han
    rcases hp.2 (2^a-1) hd with hone | hall
    · simp only [Nat.pow_one] at hlarge
      omega
    · omega

theorem int_odd_power_plus_dvd (x : Int) (t : Nat) :
    x+1 ∣ x^(2*t+1)+1 := by
  /-
  Lemma: x+1 divides every odd power of x plus one.
  Proof: For exponent one the quotient is one. Suppose
  x^(2t+1)+1=(x+1)*q. Multiplying the equation by x squared and
  subtracting x squared minus one gives
  x^(2t+3)+1=(x+1)*(x*x*q-(x-1)).
  Thus the displayed expression is a quotient at the next odd exponent.
  Induction proves the result with explicit integer witnesses. QED
  -/
  induction t with
  | zero => exact ⟨1, by simp [Int.pow_succ, Int.pow_zero]⟩
  | succ t ih =>
    rcases ih with ⟨q,hq⟩
    exists x*x*q-(x-1)
    have hstep : 2*(t+1)+1 = (2*t+1)+1+1 := by omega
    rw [hstep, Int.pow_succ, Int.pow_succ]
    have he := congrArg (fun z => x*x*z) hq
    simp only [Int.mul_add, Int.mul_one, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at he
    simp only [Int.mul_sub, Int.add_mul, Int.mul_add, Int.sub_mul,
      Int.mul_one, Int.one_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega

theorem odd_power_plus_dvd (x m : Nat) (hm : m % 2 = 1) :
    x+1 ∣ x^m+1 := by
  /-
  Lemma: If m is odd, x+1 divides x^m+1 for every natural x.
  Proof: Division by two writes m=2*t+1. Apply the integer witness
  construction for odd powers. Since both sides are natural numbers,
  integer divisibility gives natural divisibility. QED
  -/
  have he : m = 2*(m/2)+1 := by omega
  apply Int.ofNat_dvd.mp
  simp only [Int.natCast_add, Int.natCast_pow, Int.natCast_one]
  rw [he]
  exact int_odd_power_plus_dvd (x : Int) (m/2)

theorem power_of_two_exponent_of_two_pow_add_one (n : Nat) (hn : 0 < n)
    (hp : Prime (2^n+1)) : ∃ k : Nat, n = 2^k := by
  /-
  Theorem: If n is positive and 2^n+1 is prime, then n is a power
  of two. Proof: Remove factors of two from n to write n=2^k*r,
  where r is positive and odd. Put x=2^(2^k). Then 2^n+1=x^r+1,
  and oddness of r makes x+1 a divisor. If r>1, then 2^k<n, so
  1<x+1<2^n+1. This contradicts primality. Thus r=1 and n=2^k.
  QED

  The positive hypothesis matches the textbook's natural-number
  convention. It is necessary: n=0 gives the prime 2, but zero is
  not a power of two. The exponent k may be zero, allowing n=1.
  -/
  rcases odd_part_exists n hn with ⟨r, hr, hodd, _, k, he⟩
  by_cases hone : r = 1
  · exists k
    simpa only [hone, Nat.mul_one] using he
  · have hrlarge : 1 < r := by omega
    have hkpos : 0 < 2^k := Nat.pow_pos (by decide)
    have hklt : 2^k < n := by
      have h := Nat.mul_lt_mul_of_pos_left hrlarge hkpos
      rw [Nat.mul_one, ← he] at h
      exact h
    have hd := odd_power_plus_dvd (2^(2^k)) r hodd
    rw [← Nat.pow_mul, ← he] at hd
    have hxpos : 0 < 2^(2^k) := Nat.pow_pos (by decide)
    have hsmall := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hklt
    rcases hp.2 (2^(2^k)+1) hd with hOne | hWhole
    · omega
    · omega

end NumberTheory.PowerFactors
