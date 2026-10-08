import Init.Data.Nat.Dvd
import Lean.Elab.Tactic.Omega

namespace NumberTheory.CompositeRuns

def initialProduct : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * initialProduct n

theorem initialProduct_positive (n : Nat) : 0 < initialProduct n := by
  /-
  Lemma: The product of the integers from one through n is positive.
  Proof: The empty product is one. Each next product multiplies a
  positive preceding product by the positive integer n+1. Induction
  therefore proves positivity for every n. QED
  -/
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem divides_initialProduct (d n : Nat) (hd : 0 < d) (hle : d ≤ n) :
    d ∣ initialProduct n := by
  /-
  Lemma: Every positive integer at most n divides the product of the
  integers from one through n.
  Proof: Induct on n. There is no positive integer at most zero.
  At the next step, if d=n+1 it is the newly added factor. Otherwise
  d≤n, so write the preceding product as d*t by induction. The new
  product is then d*((n+1)*t), giving the required quotient. QED
  -/
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : d = n+1
    · subst d
      exact ⟨initialProduct n, rfl⟩
    · rcases ih (by omega) with ⟨t, ht⟩
      exists (n+1)*t
      rw [initialProduct, ht]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]


def Composite (m : Nat) : Prop :=
  ∃ a b : Nat, a < m ∧ b < m ∧ m = a*b

theorem initial_product_offset_composite (k d : Nat) (hd : 1 < d) (hle : d ≤ k) :
    Composite (initialProduct k+d) := by
  /-
  Lemma: If 2≤d≤k, adding d to the product of the integers from one
  through k gives a composite number.
  Proof: Write that product P as d*q, since d is one of its factors.
  Then P+d=d*(q+1). Positivity of P gives q>0, so both d and q+1
  exceed one. Moreover d<P+d because P>0, and q+1<d*(q+1) because
  d>1. Thus we have expressed P+d as a product of two smaller
  natural numbers, which is the definition of composite. QED
  -/
  have hP := initialProduct_positive k
  rcases divides_initialProduct d k (by omega) hle with ⟨q,hq⟩
  have he : initialProduct k+d = d*(q+1) := by
    rw [hq, Nat.mul_add, Nat.mul_one]
  have hqpos : 0 < q := by
    by_cases hz : q = 0
    · rw [hz, Nat.mul_zero] at hq
      omega
    · omega
  have hsmall := Nat.mul_lt_mul_of_pos_right hd (by omega : 0 < q+1)
  rw [Nat.one_mul, ← he] at hsmall
  exact ⟨d,q+1,by omega,hsmall,he⟩

end NumberTheory.CompositeRuns
