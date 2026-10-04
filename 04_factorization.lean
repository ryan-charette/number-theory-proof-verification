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

theorem common_divisor_remainder (a b n r k : Int)
    (h : a = n * b + r) (ha : k ∣ a) (hb : k ∣ b) : k ∣ r := by
  /-
  Theorem: If a = n * b + r, a common divisor of a and b divides r.
  Proof: Subtract n * b from a. A common divisor divides this integer
  linear combination, and a - n * b = r. QED
  -/
  have hd := dvd_linear k a b 1 (-n) ha hb
  rw [Int.mul_one, Int.mul_neg, Int.mul_comm b n] at hd
  have heq : a + -(n * b) = r := by omega
  rw [heq] at hd
  exact hd

theorem common_divisors_step (a b n r k : Int) (h : a = n * b + r) :
    (k ∣ a ∧ k ∣ b) ↔ (k ∣ b ∧ k ∣ r) := by
  /-
  Theorem: Replacing (a, b) by (b, r), where a = n * b + r,
  leaves the common divisors unchanged.
  Proof: The forward implication follows from the preceding theorem.
  Conversely, if k divides b and r, it divides n * b + r = a. QED
  -/
  constructor
  · intro hk
    exact ⟨hk.2, common_divisor_remainder a b n r k h hk.1 hk.2⟩
  · intro hk
    have hd := dvd_linear k b r n 1 hk.1 hk.2
    rw [Int.mul_one, Int.mul_comm b n, ← h] at hd
    exact ⟨hd, hk.1⟩

theorem least_natural (P : Nat → Prop) (h : ∃ b, P b) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b := by
  /-
  Theorem: A nonempty collection of natural numbers has a least member.
  Proof: We prove by strong induction on b that if b is a member, the
  collection has a least member. Strong induction allows us to assume
  the assertion for every natural number smaller than b.

  If some member a is smaller than b, the induction hypothesis at a
  gives a least member. If no member is smaller than b, then b itself
  is least. Finally, nonemptiness supplies a member to start with. QED
  -/
  letI := Classical.propDecidable
  have least_below : ∀ b, P b → ∃ a, P a ∧ ∀ c, P c → a ≤ c := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro hb
      by_cases hs : ∃ a, a < b ∧ P a
      · rcases hs with ⟨a, hab, ha⟩
        exact ih a hab ha
      · exists b
        constructor
        · exact hb
        · intro c hc
          apply Nat.le_of_not_lt
          intro hcb
          exact hs ⟨c, hcb, hc⟩
  rcases h with ⟨b, hb⟩
  exact least_below b hb


theorem division_exists (m n : Nat) (hn : 0 < n) :
    ∃ q r : Int, (m : Int) = (n : Int) * q + r ∧ 0 ≤ r ∧ r < (n : Int) := by
  /-
  Theorem: For a natural number m and a positive natural number n,
  there are integers q and r with m = n * q + r and 0 ≤ r < n.
  Lean includes zero among the natural numbers, so we explicitly require
  n > 0. The conclusion also holds when m = 0.

  Proof: Consider all nonnegative integers r for which m = n * q + r
  for some integer q. This collection is nonempty: q = 0 and r = m
  satisfy the equation. Choose its least member r by well-ordering,
  and choose an integer q giving the equation.

  If r ≥ n, then r - n is nonnegative and

    m = n * q + r = n * (q + 1) + (r - n).

  Thus r - n is another member of the collection. Since n > 0,
  it is smaller than r, contradicting the choice of r. Hence r < n.
  The chosen q and r have all the required properties. QED
  -/
  let P : Nat → Prop := fun r => ∃ q : Int, (m : Int) = (n : Int) * q + r
  have hnonempty : ∃ r, P r := by
    exists m
    exists (0 : Int)
    rw [Int.mul_zero, Int.zero_add]
  rcases least_natural P hnonempty with ⟨r, hr, hleast⟩
  rcases hr with ⟨q, hq⟩
  have hsmall : r < n := by
    apply Nat.lt_of_not_ge
    intro hlarge
    have hnext : P (r - n) := by
      exists q + 1
      rw [Int.mul_add, Int.mul_one]
      -- Since n ≤ r, natural subtraction agrees with integer subtraction.
      omega
    have hminimal := hleast (r - n) hnext
    -- Subtracting positive n gives a strictly smaller natural number.
    omega
  exists q, (r : Int)
  exact ⟨hq, by omega, by omega⟩


theorem dvd_refl (a : Int) : a ∣ a := by
  /-
  Theorem: Every integer divides itself.
  Proof: a = a * 1, so choose the integer 1. QED
  -/
  exists 1
  rw [Int.mul_one]

theorem dvd_zero (a : Int) : a ∣ 0 := by
  /-
  Theorem: Every integer divides zero.
  Proof: 0 = a * 0, so choose the integer 0. QED
  -/
  exists 0
  rw [Int.mul_zero]

theorem euclid_natural (a b : Nat) :
    ∃ d : Nat, (d : Int) ∣ (a : Int) ∧ (d : Int) ∣ (b : Int) ∧
      ∃ x y : Int, (a : Int) * x + (b : Int) * y = (d : Int) := by
  /-
  Theorem: The Euclidean procedure produces a nonnegative common divisor
  that is an integer linear combination of the two natural numbers.
  Proof: Use strong induction on the second number b.

  If b = 0, take d = a and coefficients 1 and 0.
  If b > 0, write a = b * q + r with 0 ≤ r < b. Apply the induction
  hypothesis to b and r. It supplies a common divisor d and integers
  x and y with b * x + r * y = d. The preceding common-divisor theorem
  shows that d also divides a. Back-substitution gives

    d = b * x + (a - b * q) * y = a * y + b * (x - q * y).

  These are the required new coefficients. The smaller nonnegative
  remainder ensures that the procedure terminates. QED
  -/
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb : b = 0
    · subst b
      exists a
      refine ⟨dvd_refl a, dvd_zero a, ?_⟩
      exists 1, 0
      rw [Int.mul_one, Int.mul_zero, Int.add_zero]
    · have hbpos : 0 < b := by omega
      rcases division_exists a b hbpos with ⟨q, r, heq, hr, hrb⟩
      have hrnat : (r.toNat : Int) = r := Int.toNat_of_nonneg hr
      rcases ih r.toNat (by omega) b with ⟨d, hdb, hdr, x, y, hxy⟩
      rw [hrnat] at hdr hxy
      have hda := ((common_divisors_step a b q r d
        (by rw [Int.mul_comm]; exact heq)).mpr ⟨hdb, hdr⟩).1
      exists d
      refine ⟨hda, hdb, ?_⟩
      exists y, x - q * y
      have htimes := congrArg (fun t : Int => t * y) heq
      change (a : Int) * y = ((b : Int) * q + r) * y at htimes
      rw [Int.add_mul, Int.mul_assoc] at htimes
      rw [Int.mul_sub]
      omega


/-
A prime has only the positive divisors one and itself. We verify below
that this is equivalent to having no product of two smaller natural
numbers. A composite number has such a product decomposition.
-/
def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def Composite (n : Nat) : Prop := ∃ a b : Nat, a < n ∧ b < n ∧ n = a * b

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

theorem prime_iff_no_smaller_factors (p : Nat) :
    Prime p ↔ 1 < p ∧ ¬ Composite p := by
  /-
  Theorem: A number is prime exactly when it is greater than one and
  is not a product of two smaller natural numbers.
  Proof: For a prime p, a factor a of p must be one or p. In a smaller
  factorization, a cannot be p; if a=1 the other factor would be p,
  also impossible. Conversely, a nonprime number greater than one
  has the smaller factorization provided by the preceding theorem.
  QED
  -/
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro hc
    rcases hc with ⟨a, b, ha, hb, heq⟩
    rcases hp.2 a ⟨b, heq⟩ with h₁ | h₂
    · rw [h₁, Nat.one_mul] at heq
      omega
    · omega
  · intro h
    apply Classical.byContradiction
    intro hp
    rcases nonprime_factors p h.1 hp with ⟨a, b, _, ha, _, hb, heq⟩
    exact h.2 ⟨a, b, ha, hb, heq⟩

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

theorem composite_small_prime (n : Nat) (hn : 1 < n) (hp : ¬ Prime n) :
    ∃ p : Nat, Prime p ∧ p ∣ n ∧ p * p ≤ n := by
  /-
  Theorem: A nonprime number greater than one has a prime divisor
  whose square is at most the number.
  Proof: Write n=a*b with both factors greater than one. The smaller
  factor has a prime divisor p. Then p is at most both factors, so
  p*p≤a*b=n. It divides n because it divides one of the factors. QED
  -/
  rcases nonprime_factors n hn hp with ⟨a, b, ha, _, hb, _, heq⟩
  by_cases hab : a ≤ b
  · rcases prime_divisor a ha with ⟨p, hpp, hd⟩
    have hpa := Nat.le_of_dvd (by omega : 0 < a) hd
    rcases hd with ⟨t, ht⟩
    exists p
    refine ⟨hpp, ⟨t * b, by rw [heq, ht, Nat.mul_assoc]⟩, ?_⟩
    rw [heq]
    exact Nat.mul_le_mul hpa (by omega)
  · rcases prime_divisor b hb with ⟨p, hpp, hd⟩
    have hpb := Nat.le_of_dvd (by omega : 0 < b) hd
    rcases hd with ⟨t, ht⟩
    exists p
    refine ⟨hpp, ⟨t * a, ?_⟩, ?_⟩
    · calc
        n = b * a := by rw [heq, Nat.mul_comm]
        _ = p * (t * a) := by rw [ht, Nat.mul_assoc]
    · rw [heq]
      exact Nat.mul_le_mul (by omega) hpb

theorem prime_trial_bound (n : Nat) (hn : 1 < n) :
    Prime n ↔ ∀ p : Nat, Prime p → p * p ≤ n → ¬ p ∣ n := by
  /-
  Theorem: A number greater than one is prime exactly when no prime
  whose square is at most n divides n. The condition p*p≤n expresses
  p≤sqrt(n) without introducing real square roots.
  Proof: If n is prime, a prime divisor p must equal n. But p>1
  implies p*p>p=n, contradicting the bound. Conversely, a nonprime
  number has a prime divisor meeting the bound by the previous theorem.
  QED
  -/
  constructor
  · intro h p hp hbound hd
    rcases h.2 p hd with h₁ | h₂
    · have hpos := hp.1
      omega
    · have hlarge := Nat.mul_lt_mul_of_pos_left hp.1 (by omega : 0 < p)
      rw [Nat.mul_one] at hlarge
      omega
  · intro h
    apply Classical.byContradiction
    intro hnot
    rcases composite_small_prime n hn hnot with ⟨p, hp, hd, hbound⟩
    exact h p hp hbound hd

theorem prime_dvd_mul (p a b : Nat) (hp : Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  /-
  Theorem: A prime dividing a product divides at least one factor.
  Proof: The Euclidean construction for p and a supplies a common
  divisor d and integers x,y with p*x+a*y=d. Since d divides prime p,
  it equals one or p. If d=p, then p divides a. If d=1, multiply by b:

    b = p*(x*b) + (a*b)*y.

  Each term on the right is divisible by p, so p divides b. QED
  -/
  rcases euclid_natural p a with ⟨d, hdp, hda, x, y, hxy⟩
  rcases hp.2 d (Int.ofNat_dvd.mp hdp) with hd₁ | hdp'
  · right
    rw [hd₁] at hxy
    have hab : (p : Int) ∣ (a : Int) * (b : Int) := Int.ofNat_dvd.mpr h
    have hd := dvd_linear p p ((a : Int) * b) (x * b) y (dvd_refl p) hab
    have heq := congrArg (fun t : Int => t * (b : Int)) hxy
    change ((p : Int) * x + (a : Int) * y) * b = 1 * (b : Int) at heq
    rw [Int.add_mul, Int.one_mul, Int.mul_assoc (p : Int),
      Int.mul_right_comm (a : Int) y (b : Int)] at heq
    rw [heq] at hd
    exact Int.ofNat_dvd.mp hd
  · left
    rw [hdp'] at hda
    exact Int.ofNat_dvd.mp hda

def product : List Nat → Nat
  | [] => 1
  | p :: ps => p * product ps

def PrimeFactors (ps : List Nat) : Prop := ∀ p ∈ ps, Prime p

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

theorem prime_divides_prime_list (p : Nat) (ps : List Nat) (hp : Prime p)
    (hps : PrimeFactors ps) (hd : p ∣ product ps) : p ∈ ps := by
  /-
  Lemma: A prime dividing a product of primes occurs among those primes.
  Proof: Induct on the list. The empty product is one, which no prime
  divides. For a first prime q, the product lemma says p divides q
  or the remaining product. In the first case primality of q forces
  p=q; in the second case use the induction hypothesis. QED
  -/
  induction ps with
  | nil =>
    have hle := Nat.le_of_dvd (by decide : 0 < 1) hd
    have hp₁ := hp.1
    omega
  | cons q qs ih =>
    rcases prime_dvd_mul p q (product qs) hp hd with hq | htail
    · rcases (hps q (by simp)).2 p hq with hp₁ | hpq
      · have hpos := hp.1
        omega
      · simp [hpq]
    · exact List.mem_cons_of_mem q (ih (fun t ht => hps t (List.mem_cons_of_mem q ht)) htail)

theorem prime_multiple_match (p k : Nat) (qs : List Nat) (hp : Prime p)
    (hqs : PrimeFactors qs) (h : p * k = product qs) : p ∈ qs := by
  /-
  Lemma: If a multiple of a prime is a product of primes, that prime
  equals an entry of the product. Proof: The displayed equation gives
  the divisibility witness k. Apply the preceding matching lemma. QED
  -/
  exact prime_divides_prime_list p qs hp hqs ⟨k, h.symm⟩

end NumberTheory.Factorization
