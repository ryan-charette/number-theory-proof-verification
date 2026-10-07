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

def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem nonprime_factors (n : Nat) (hn : 1 < n) (hp : ¬ Prime n) :
    ∃ a b : Nat, 1 < a ∧ a < n ∧ 1 < b ∧ b < n ∧ n = a * b := by
  /-
  Theorem: A nonprime number greater than one is a product of two
  numbers strictly between one and itself.
  Proof: Since n is not prime, it has a divisor a other than one and n.
  Write n=a*b. Neither factor is zero. The factor b cannot be one,
  since that would give a=n. Both factors are therefore at least two.
  Each divides n and is at most n; equality would force the other
  factor to be one. Thus both factors are strictly smaller than n. QED
  -/
  have hex : ∃ a : Nat, a ∣ n ∧ a ≠ 1 ∧ a ≠ n := by
    apply Classical.byContradiction
    intro he
    apply hp
    constructor
    · exact hn
    · intro a ha
      by_cases h₁ : a = 1
      · exact Or.inl h₁
      · by_cases h₂ : a = n
        · exact Or.inr h₂
        · exact False.elim (he ⟨a, ha, h₁, h₂⟩)
  rcases hex with ⟨a, ha, ha₁, han⟩
  rcases ha with ⟨b, heq⟩
  have ha₀ : a ≠ 0 := by intro hz; rw [hz, Nat.zero_mul] at heq; omega
  have hb₀ : b ≠ 0 := by intro hz; rw [hz, Nat.mul_zero] at heq; omega
  have hb₁ : b ≠ 1 := by intro ho; rw [ho, Nat.mul_one] at heq; omega
  have hal := Nat.le_of_dvd (by omega : 0 < n) (show a ∣ n from ⟨b, heq⟩)
  have hbl := Nat.le_of_dvd (by omega : 0 < n) (show b ∣ n from ⟨a, by rw [Nat.mul_comm]; exact heq⟩)
  have hbn : b ≠ n := by
    intro hbn
    have ht : b * a = b * 1 := by rw [Nat.mul_one, Nat.mul_comm]; omega
    have haeq := Nat.eq_of_mul_eq_mul_left (by omega : 0 < b) ht
    exact ha₁ haeq
  exists a, b
  exact ⟨by omega, by omega, by omega, by omega, heq⟩



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

end NumberTheory.PowerFactors
