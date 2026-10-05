import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

/-
This file develops applications of prime factors to divisibility and
integer equations. Supporting arithmetic and factorization results are
proved here so the file is independent of the earlier source files.
-/

namespace NumberTheory.DivisibilityTests

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
theorem dvd_trans (a b c : Int) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  /-
  Theorem: Divisibility is transitive.
  Proof: If b = a * u and c = b * v, then c = a * (u * v).
  The integer u * v supplies the required witness. QED
  -/
  rcases hab with ⟨u, hu⟩
  rcases hbc with ⟨v, hv⟩
  exists u * v
  rw [hv, hu, Int.mul_assoc]
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
theorem euclid_integer (a b : Int) :
    ∃ d : Nat, (d : Int) ∣ a ∧ (d : Int) ∣ b ∧
      ∃ x y : Int, a * x + b * y = (d : Int) := by
  /-
  Theorem: The Euclidean construction also works for arbitrary integers.
  Proof: Apply the natural-number procedure to the absolute values.
  Changing a sign does not change divisibility. If the resulting
  coefficients are x and y, multiply them by the signs of a and b.
  Since a * sign(a) = |a|, the same linear combination gives d. QED
  -/
  rcases euclid_natural a.natAbs b.natAbs with ⟨d, ha, hb, x, y, hxy⟩
  exists d
  constructor
  · rcases ha with ⟨u, hu⟩
    exists a.sign * u
    calc
      a = a.sign * (a.natAbs : Int) := (Int.sign_mul_natAbs a).symm
      _ = (d : Int) * (a.sign * u) := by rw [hu, Int.mul_left_comm]
  · constructor
    · rcases hb with ⟨v, hv⟩
      exists b.sign * v
      calc
        b = b.sign * (b.natAbs : Int) := (Int.sign_mul_natAbs b).symm
        _ = (d : Int) * (b.sign * v) := by rw [hv, Int.mul_left_comm]
    · exists a.sign * x, b.sign * y
      rw [← Int.mul_assoc, Int.mul_sign, ← Int.mul_assoc, Int.mul_sign]
      exact hxy

/-
The Euclidean construction supplies a nonnegative common divisor together
with coefficients. We name that number gcd(a,b). The next proofs verify
that it is the greatest common divisor in the ordinary numerical sense.
We also set gcd(0,0) = 0 through this construction; statements that require
a positive greatest divisor explicitly exclude the pair (0,0).
-/
noncomputable def gcd (a b : Int) : Int := (Classical.choose (euclid_integer a b) : Nat)

theorem gcd_data (a b : Int) :
    0 ≤ gcd a b ∧ gcd a b ∣ a ∧ gcd a b ∣ b ∧
      ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The constructed gcd is nonnegative, divides both inputs,
  and is an integer linear combination of them.
  Proof: These are exactly the properties supplied by the Euclidean
  construction used in its definition. QED
  -/
  constructor
  · unfold gcd
    omega
  · exact Classical.choose_spec (euclid_integer a b)
theorem gcd_positive (a b : Int) (h : a ≠ 0 ∨ b ≠ 0) : 0 < gcd a b := by
  /-
  Theorem: The gcd is positive when the inputs are not both zero.
  Proof: It is nonnegative. If it were zero, divisibility of a and b
  would express both as zero times an integer, forcing a = b = 0.
  This contradicts the hypothesis. QED
  -/
  rcases gcd_data a b with ⟨hn, ⟨u, hu⟩, ⟨v, hv⟩, hxy⟩
  by_cases hz : gcd a b = 0
  · rw [hz, Int.zero_mul] at hu hv
    rcases h with ha | hb
    · exact False.elim (ha hu)
    · exact False.elim (hb hv)
  · omega
theorem divisor_le_positive (e d : Int) (hd : 0 < d) (he : e ∣ d) : e ≤ d := by
  /-
  Theorem: A divisor of a positive integer is at most that integer.
  Proof: A nonpositive divisor is already smaller. Otherwise write
  d = e * k with e > 0. If k ≤ 0 then d ≤ 0, a contradiction.
  Thus the integer k is at least 1, and d = e * k ≥ e * 1 = e. QED
  -/
  by_cases hep : 0 < e
  · rcases he with ⟨k, hk⟩
    have hkpos : 0 < k := by
      by_cases hkn : k ≤ 0
      · have hm := Int.mul_le_mul_of_nonneg_left hkn (Int.le_of_lt hep)
        rw [Int.mul_zero, ← hk] at hm
        omega
      · omega
    have hm := Int.mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (Int.le_of_lt hep)
    rw [Int.mul_one, ← hk] at hm
    exact hm
  · omega
theorem gcd_greatest (a b : Int) (h : a ≠ 0 ∨ b ≠ 0)
    (e : Int) (ha : e ∣ a) (hb : e ∣ b) : e ≤ gcd a b := by
  /-
  Theorem: Every common divisor is at most the constructed gcd.
  Proof: A common divisor divides every integer linear combination,
  hence divides the gcd by its Euclidean representation. Since the
  gcd is positive, the preceding bound gives the result. QED
  -/
  rcases (gcd_data a b).2.2.2 with ⟨x, y, hxy⟩
  have hd := dvd_linear e a b x y ha hb
  rw [hxy] at hd
  exact divisor_le_positive e (gcd a b) (gcd_positive a b h) hd
theorem coprime_bezout (a b : Int) (h : gcd a b = 1) :
    ∃ x y : Int, a * x + b * y = 1 := by
  /-
  Theorem: Relatively prime integers have an integer linear combination
  equal to one. Here relatively prime means that their gcd equals one.
  Proof: The Euclidean back-substitution coefficients give the gcd.
  Substituting the hypothesis changes that right side to one. QED
  -/
  rcases (gcd_data a b).2.2.2 with ⟨x, y, hxy⟩
  exists x, y
  rw [h] at hxy
  exact hxy
theorem coprime_of_bezout (a b x y : Int) (h : a * x + b * y = 1) :
    gcd a b = 1 := by
  /-
  Theorem: An integer linear combination equal to one implies coprimality.
  Proof: The gcd divides both inputs, so divides the combination one.
  It is nonnegative and cannot be zero, since zero does not divide one.
  A positive divisor of one is at most one, hence must equal one. QED
  -/
  have hg := gcd_data a b
  have hd := dvd_linear (gcd a b) a b x y hg.2.1 hg.2.2.1
  rw [h] at hd
  have hle := divisor_le_positive (gcd a b) 1 (by decide) hd
  have hne : gcd a b ≠ 0 := by
    intro hz
    rcases hd with ⟨k, hk⟩
    rw [hz, Int.zero_mul] at hk
    omega
  omega
theorem coprime_iff_bezout (a b : Int) :
    gcd a b = 1 ↔ ∃ x y : Int, a * x + b * y = 1 := by
  /-
  Theorem: Coprimality is equivalent to an integer linear combination
  equal to one. Proof: Apply the two implications just proved. QED
  -/
  constructor
  · exact coprime_bezout a b
  · intro h
    rcases h with ⟨x, y, hxy⟩
    exact coprime_of_bezout a b x y hxy
theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The gcd of two integers is an integer linear combination.
  Proof: These are the coefficients constructed by the Euclidean
  procedure and back-substitution above. The construction also covers
  the harmless extra case a = b = 0. QED
  -/
  exact (gcd_data a b).2.2.2
theorem coprime_swap (a b : Int) (h : gcd a b = 1) : gcd b a = 1 := by
  /-
  Theorem: Coprimality is unchanged by interchanging the inputs.
  Proof: If a * x + b * y = 1, commutativity of addition gives
  b * y + a * x = 1. Apply the coprimality criterion. QED
  -/
  rcases coprime_bezout a b h with ⟨x, y, hxy⟩
  apply coprime_of_bezout b a y x
  rw [Int.add_comm]
  exact hxy
theorem coprime_dvd_cancel (a b c : Int) (hdiv : a ∣ b * c)
    (hcop : gcd a b = 1) : a ∣ c := by
  /-
  Theorem: If a divides b * c and a is relatively prime to b, then a
  divides c. Proof: Choose x,y with a * x + b * y = 1. Multiply by c:

    c = a * (x * c) + (b * c) * y.

  Both terms on the right are divisible by a, so their sum is too. QED
  -/
  rcases coprime_bezout a b hcop with ⟨x, y, hxy⟩
  have hd := dvd_linear a a (b * c) (x * c) y (dvd_refl a) hdiv
  have heq := congrArg (fun t : Int => t * c) hxy
  change (a * x + b * y) * c = 1 * c at heq
  rw [Int.add_mul, Int.one_mul, Int.mul_assoc a, Int.mul_right_comm b y c] at heq
  rw [heq] at hd
  exact hd
theorem coprime_product_dvd (a b n : Int) (ha : a ∣ n) (hb : b ∣ n)
    (hcop : gcd a b = 1) : a * b ∣ n := by
  /-
  Theorem: If relatively prime a and b both divide n, then a * b divides n.
  Proof: Write n = a * k. Since b divides a * k and is relatively prime
  to a, it divides k. Writing k = b * t gives n = (a * b) * t. QED
  -/
  rcases ha with ⟨k, hk⟩
  have hbk : b ∣ a * k := by rw [← hk]; exact hb
  rcases coprime_dvd_cancel b a k hbk (coprime_swap a b hcop) with ⟨t, ht⟩
  exists t
  rw [hk, ht, Int.mul_assoc]
theorem coprime_product (a b n : Int) (ha : gcd a n = 1)
    (hb : gcd b n = 1) : gcd (a * b) n = 1 := by
  /-
  Theorem: A product of two integers each relatively prime to n is
  relatively prime to n. Proof: Choose a*x+n*y=1 and b*u+n*v=1.
  Multiplying and collecting the terms containing n gives

    (a*b)*(x*u) + n*(a*x*v + b*y*u + n*y*v) = 1.

  The coprimality criterion applies to this linear combination. QED
  -/
  rcases coprime_bezout a n ha with ⟨x, y, hxy⟩
  rcases coprime_bezout b n hb with ⟨u, v, huv⟩
  apply coprime_of_bezout (a * b) n (x * u) (a * x * v + b * y * u + n * y * v)
  calc
    _ = (a * x + n * y) * (b * u + n * v) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      omega
    _ = 1 := by rw [hxy, huv]; rfl
theorem gcd_quotients (a b : Int) :
    a = gcd a b * (a / gcd a b) ∧ b = gcd a b * (b / gcd a b) := by
  /-
  Theorem: Dividing either input by its gcd gives an exact integer factor.
  Proof: The gcd divides both numbers. Exact division of an integer
  multiple recovers its factor, so multiplication by the gcd recovers
  the original number. Only this basic exact-division identity is used.
  QED
  -/
  exact ⟨(Int.mul_ediv_cancel' (gcd_data a b).2.1).symm,
    (Int.mul_ediv_cancel' (gcd_data a b).2.2.1).symm⟩
theorem reduced_coprime (a b : Int) (hne : a ≠ 0 ∨ b ≠ 0) :
    gcd (a / gcd a b) (b / gcd a b) = 1 := by
  /-
  Theorem: Removing the gcd leaves relatively prime integers.
  Proof: Write a=g*A and b=g*B. Bezout gives a*x+b*y=g, hence
  g*(A*x+B*y)=g. Since g is positive, cancel g to get A*x+B*y=1.
  The coprimality criterion applies. QED
  -/
  rcases bezout a b with ⟨x, y, hxy⟩
  have hf := gcd_quotients a b
  have hp := gcd_positive a b hne
  apply coprime_of_bezout (a / gcd a b) (b / gcd a b) x y
  apply Int.eq_of_mul_eq_mul_left (a := gcd a b) (by omega)
  rw [Int.mul_add, ← Int.mul_assoc, ← hf.1, ← Int.mul_assoc, ← hf.2, Int.mul_one]
  exact hxy
theorem gcd_eq_of_combination (a b d : Int) (hd : 0 < d)
    (ha : d ∣ a) (hb : d ∣ b) (hxy : ∃ x y : Int, a * x + b * y = d) :
    gcd a b = d := by
  /-
  Theorem: A positive common divisor that is a linear combination of
  the inputs is their gcd. Proof: The inputs cannot both vanish,
  because the combination is positive. Thus d is at most their gcd.
  Conversely, the gcd divides the combination d, so is at most d.
  These two inequalities prove equality. QED
  -/
  rcases hxy with ⟨x, y, heq⟩
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_cases ha₀ : a = 0
    · right
      intro hb₀
      rw [ha₀, hb₀, Int.zero_mul, Int.zero_mul, Int.add_zero] at heq
      omega
    · exact Or.inl ha₀
  have hle := gcd_greatest a b hne d ha hb
  have hdiv := dvd_linear (gcd a b) a b x y (gcd_data a b).2.1 (gcd_data a b).2.2.1
  rw [heq] at hdiv
  have hge := divisor_le_positive (gcd a b) d hd hdiv
  omega
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
theorem product_perm (xs ys : List Nat) (h : List.Perm xs ys) : product xs = product ys := by
  /-
  Lemma: Reordering factors does not change their product.
  Proof: A permutation is built from keeping a first entry, exchanging
  adjacent entries, and composing reorderings. Keeping an entry uses
  the equality for the tails; exchange uses commutativity and
  associativity of multiplication; composition uses equality transitivity.
  QED
  -/
  induction h with
  | nil => rfl
  | cons a h ih => rw [product, product, ih]
  | swap a b xs => simp only [product, Nat.mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem factorization_unique (xs ys : List Nat)
    (hxs : PrimeFactors xs) (hys : PrimeFactors ys) (h : product xs = product ys) :
    List.Perm xs ys := by
  /-
  Theorem: Two prime factorizations of the same number agree up to order.
  Proof: Induct on the first list. If it is empty, its product is one.
  A nonempty prime list on the other side would have a prime divisor
  of one, so that list must also be empty.

  Otherwise let p be the first prime. The matching lemma finds p in
  the second list. Move this occurrence to the front and remove it
  from both lists. Cancelling positive p leaves equal products for
  the shorter lists. Induction matches their entries. Restoring p and
  undoing the reordering proves the result. QED
  -/
  letI : BEq Nat := instBEqOfDecidableEq
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons q qs =>
      have hq := (hys q (by simp)).1
      have hd : q ∣ 1 := ⟨product qs, h⟩
      have hle := Nat.le_of_dvd (by decide : 0 < 1) hd
      omega
  | cons p ps ih =>
    have hp := hxs p (by simp)
    have hp₁ := hp.1
    have hps : PrimeFactors ps := fun q hq => hxs q (List.mem_cons_of_mem p hq)
    have hmem := prime_multiple_match p (product ps) ys hp hys h
    have hperm := List.perm_cons_erase hmem
    have heq := product_perm ys (p :: ys.erase p) hperm
    change p * product ps = product ys at h
    change product ys = p * product (ys.erase p) at heq
    have hcancel := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p) (h.trans heq)
    have htail : PrimeFactors (ys.erase p) := fun q hq => hys q (List.mem_of_mem_erase hq)
    exact (List.Perm.cons p (ih (ys.erase p) hps htail hcancel)).trans hperm.symm
theorem factorization_multiplicities (xs ys : List Nat)
    (hxs : PrimeFactors xs) (hys : PrimeFactors ys) (h : product xs = product ys) :
    xs.length = ys.length ∧ ∀ p : Nat, (p ∈ xs ↔ p ∈ ys) ∧ xs.count p = ys.count p := by
  /-
  Corollary: Equal prime products have exactly the same primes with
  exactly the same multiplicities. Proof: Uniqueness gives a reordering
  between the lists. Reordering preserves length, membership, and the
  number of times each prime occurs. These occurrence counts are the
  exponents when repeated factors are collected into prime powers. QED
  -/
  have hp := factorization_unique xs ys hxs hys h
  refine ⟨hp.length_eq, ?_⟩
  intro p
  exact ⟨hp.mem_iff, hp.countP_eq (fun q => q == p)⟩
theorem product_replicate (p r : Nat) : product (List.replicate r p) = p ^ r := by
  /-
  Lemma: Repeating the factor p exactly r times gives p to the power r.
  Proof: Induct on r. With no factors, both sides equal one. Adding
  another p multiplies the previous product by p, giving the next
  power. Thus repeated entries in a factor list represent powers,
  with the occurrence count as exponent. QED
  -/
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, product, ih, Nat.pow_succ, Nat.mul_comm]

theorem prime_product_positive (ps : List Nat) (hps : PrimeFactors ps) : 0 < product ps := by
  /-
  Lemma: A product of primes is positive, including the empty product.
  Proof: The empty product is one. For a nonempty list, the first
  prime is positive and the tail product is positive by induction.
  Multiplying two positive numbers gives a positive number. QED
  -/
  induction ps with
  | nil => decide
  | cons p ps ih =>
    exact Nat.mul_pos (by have := (hps p (by simp)).1; omega)
      (ih (fun q hq => hps q (by simp [hq])))

end NumberTheory.DivisibilityTests
