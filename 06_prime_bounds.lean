import Init.Data.Nat.Dvd
import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Omega

/-
Elementary constructions of primes beyond a bound. All supporting
results are proved here, independently of the other source files.
-/

namespace NumberTheory.PrimeBounds


def Coprime (a b : Nat) : Prop := ∀ d : Nat, d ∣ a → d ∣ b → d = 1

theorem consecutive_coprime (n : Nat) : Coprime n (n+1) := by
  /-
  Theorem: Consecutive natural numbers are coprime.
  Proof: A common divisor d divides both n and n+1, so it divides
  their difference one. A natural divisor of one is one. Hence the
  only common divisor is one, which says their greatest common
  divisor is one. This formulation also includes n=0. QED

  We express coprimality directly by its common-divisor property;
  no library gcd is needed in this file.
  -/
  intro d hd hn
  have hdiv := Nat.dvd_sub (by omega : n ≤ n+1) hn hd
  have hone : d ∣ 1 := by
    rw [show n+1-n=1 by omega] at hdiv
    exact hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < 1) hone
  rcases hone with ⟨t, ht⟩
  have hne : d ≠ 0 := by intro hz; simp [hz] at ht
  omega



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


theorem avoids_small_divisors (k : Nat) :
    ∃ n : Nat, 1 < n ∧ ∀ d : Nat, 1 < d → d ≤ k → ¬ d ∣ n := by
  /-
  Theorem: For any bound k, there is a number greater than one with
  no divisor between two and k, inclusive.
  Proof: Let P be the product of the integers from one through k,
  and take n=P+1. Positivity of P gives n>1. Every d between two
  and k divides P. If it also divided P+1, coprimality of these
  consecutive integers would force d=1, a contradiction. QED

  The inclusive upper bound strengthens the version with d<k.
  -/
  exists initialProduct k + 1
  constructor
  · have := initialProduct_positive k
    omega
  · intro d hd hle hdiv
    have he := consecutive_coprime (initialProduct k) d
      (divides_initialProduct d k (by omega) hle) hdiv
    omega

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

theorem prime_divisor (n : Nat) (hn : 1 < n) :
    ∃ p : Nat, Prime p ∧ p ∣ n := by
  /-
  Theorem: Every natural number greater than one has a prime divisor.
  Proof: Use strong induction on n. If n is prime, take n itself.
  Otherwise n=a*b with 1<a<n. By induction a has a prime divisor p.
  If a=p*t, then n=p*(t*b), so p also divides n. QED
  -/
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hp : Prime n
    · exact ⟨n, hp, ⟨1, by rw [Nat.mul_one]⟩⟩
    · rcases nonprime_factors n hn hp with ⟨a, b, ha, han, _, _, heq⟩
      rcases ih a han ha with ⟨p, hpp, t, ht⟩
      exists p
      constructor
      · exact hpp
      · exists t * b
        rw [heq, ht, Nat.mul_assoc]


theorem prime_above (k : Nat) : ∃ p : Nat, Prime p ∧ k < p := by
  /-
  Theorem: There is a prime greater than every prescribed bound k.
  Proof: Construct n>1 with no divisor between two and k. It has
  a prime divisor p. Since p>1, the condition on n rules out p≤k.
  Thus p>k. Notice that n itself need not be prime. QED
  -/
  rcases avoids_small_divisors k with ⟨n, hn, havoid⟩
  rcases prime_divisor n hn with ⟨p, hp, hd⟩
  refine ⟨p, hp, ?_⟩
  by_cases hle : p ≤ k
  · exact False.elim (havoid p hp.1 hle hd)
  · omega


def listBound : List Nat → Nat
  | [] => 0
  | a :: xs => max a (listBound xs)

theorem member_le_listBound (a : Nat) (xs : List Nat) (ha : a ∈ xs) :
    a ≤ listBound xs := by
  /-
  Lemma: Every member of a finite list is bounded by its recursively
  computed maximum. Proof: The empty case has no member. In a
  nonempty list, a member is either the first entry or belongs to
  the tail. The maximum bounds the first entry directly and bounds
  the tail's maximum, which bounds every tail entry by induction.
  QED
  -/
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with he | ht
    · subst a
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)


theorem primes_not_finitely_listed (xs : List Nat) :
    ∃ p : Nat, Prime p ∧ p ∉ xs := by
  /-
  Theorem: There are infinitely many primes.
  Proof: Any proposed finite list is bounded by its maximum. Choose
  a prime greater than that maximum. It cannot occur on the list.
  Thus no finite list can contain all primes. QED

  We state infinitude as failure of every finite list to exhaust the
  primes, avoiding any set-theoretic library or cardinality machinery.
  -/
  rcases prime_above (listBound xs) with ⟨p, hp, hlarge⟩
  refine ⟨p, hp, ?_⟩
  intro hm
  have hle := member_le_listBound p xs hm
  omega

def product : List Nat → Nat
  | [] => 1
  | p :: ps => p * product ps

theorem product_append (xs ys : List Nat) : product (xs ++ ys) = product xs * product ys := by
  /-
  Lemma: Joining two lists multiplies their products.
  Proof: Induct on the first list. An empty list contributes one.
  For a first entry p, use the induction hypothesis for the remaining
  list and reassociate p*(product(xs)*product(ys)). QED
  -/
  induction xs with
  | nil => rw [List.nil_append, product, Nat.one_mul]
  | cons p ps ih => rw [List.cons_append, product, product, ih, Nat.mul_assoc]

def PrimeFactors (ps : List Nat) : Prop := ∀ p ∈ ps, Prime p

theorem factorization_exists (n : Nat) (hn : 1 < n) :
    ∃ ps : List Nat, PrimeFactors ps ∧ product ps = n := by
  /-
  Theorem: Every natural number greater than one is a finite product
  of primes. Proof: Use strong induction. A prime n has the one-entry
  factorization [n]. Otherwise write n=a*b with 1<a,b<n. Induction
  gives prime lists for a and b. Concatenate them: all entries remain
  prime and their product is a*b=n. QED
  -/
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hp : Prime n
    · exists [n]
      constructor
      · intro p hmem
        have heq : p = n := by simpa using hmem
        rw [heq]
        exact hp
      · rw [product, product, Nat.mul_one]
    · rcases nonprime_factors n hn hp with ⟨a, b, ha, han, hb, hbn, heq⟩
      rcases ih a han ha with ⟨xs, hxs, hx⟩
      rcases ih b hbn hb with ⟨ys, hys, hy⟩
      exists xs ++ ys
      constructor
      · intro p hm
        rcases List.mem_append.mp hm with hleft | hright
        · exact hxs p hleft
        · exact hys p hright
      · rw [product_append, hx, hy, ← heq]


theorem product_one_mod_four (xs : List Nat) (h : ∀ a ∈ xs, a % 4 = 1) :
    product xs % 4 = 1 := by
  /-
  Theorem: A finite product of numbers congruent to one modulo four
  is itself congruent to one modulo four.
  Proof: Induct on the number of factors. The empty product is one.
  For a nonempty list, its first factor and its tail product both
  have remainder one. Multiplying numbers 4u+1 and 4v+1 gives
  4*(4*u*v+u+v)+1, so the new product also has remainder one. QED

  Remainder one expresses congruence to one, as in elementary division.
  -/
  induction xs with
  | nil => decide
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    rw [product, Nat.mul_mod, ha, ht]


theorem member_divides_product (p : Nat) (xs : List Nat) (hp : p ∈ xs) :
    p ∣ product xs := by
  /-
  Lemma: Every entry of a finite factor list divides its product.
  Proof: Induct on the list. If p is the first entry, the tail product
  is the quotient. Otherwise the tail product equals p*t by induction.
  Multiplying by the first entry a gives p*(a*t), the required witness.
  QED
  -/
  induction xs with
  | nil => cases hp
  | cons a xs ih =>
    rcases List.mem_cons.mp hp with he | hm
    · subst p
      exact ⟨product xs, rfl⟩
    · rcases ih hm with ⟨t, ht⟩
      exists a*t
      rw [product, ht]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

end NumberTheory.PrimeBounds
