import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Lean.Elab.Tactic.Omega

/-
We study common divisors and integer linear equations using integer
witnesses, ordinary arithmetic, and the Euclidean reduction. Supporting
results are proved here so that this file can be used independently.
-/

namespace NumberTheory.CommonDivisors

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

theorem gcd_step (a b n r : Int) (h : a = n * b + r)
    (hne : a ≠ 0 ∨ b ≠ 0) : gcd a b = gcd b r := by
  /-
  Theorem: A Euclidean step leaves the gcd unchanged.
  Proof: Both pairs have exactly the same common divisors. Each gcd
  is therefore a common divisor of the other pair, so each is at most
  the other. Equality follows. The new pair cannot be (0,0), since
  then a = n * 0 + 0 = 0 as well. QED
  -/
  have hbr : b ≠ 0 ∨ r ≠ 0 := by
    by_cases hb : b = 0
    · right
      intro hr
      rw [hb, hr, Int.mul_zero, Int.add_zero] at h
      rcases hne with ha | hb'
      · exact ha h
      · exact hb' hb
    · exact Or.inl hb
  have hab := (gcd_data a b).2
  have hbrd := (gcd_data b r).2
  have h₁ := (common_divisors_step a b n r (gcd a b) h).mp ⟨hab.1, hab.2.1⟩
  have h₂ := (common_divisors_step a b n r (gcd b r) h).mpr ⟨hbrd.1, hbrd.2.1⟩
  have hl := gcd_greatest b r hbr (gcd a b) h₁.1 h₁.2
  have hr := gcd_greatest a b hne (gcd b r) h₂.1 h₂.2
  omega

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
  have hn := hg.1
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

def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a - b

theorem congruence_cancel (a b c n : Int) (h : Congruent (a * c) (b * c) n)
    (hc : gcd c n = 1) : Congruent a b n := by
  /-
  Theorem: A factor relatively prime to the modulus can be cancelled
  from a congruence. Proof: The hypothesis says n divides
  a*c-b*c = c*(a-b). Since n is relatively prime to c, the divisibility
  cancellation theorem shows n divides a-b. The modulus stays positive.
  QED
  -/
  constructor
  · exact h.1
  · have hd : n ∣ c * (a - b) := by
      rw [Int.mul_sub, Int.mul_comm c a, Int.mul_comm c b]
      exact h.2
    exact coprime_dvd_cancel n c (a - b) hd (coprime_swap c n hc)

theorem linear_solvable_iff (a b c : Int) :
    (∃ x y : Int, a * x + b * y = c) ↔ gcd a b ∣ c := by
  /-
  Theorem: An integer linear equation a*x+b*y=c is solvable exactly
  when the gcd divides c. Proof: A solution expresses c as a linear
  combination, so the gcd divides it. Conversely, write c=gcd(a,b)*t
  and choose a*u+b*v=gcd(a,b). Multiplying this identity by t gives
  the solution x=u*t and y=v*t. QED
  -/
  constructor
  · intro h
    rcases h with ⟨x, y, hxy⟩
    have hd := dvd_linear (gcd a b) a b x y (gcd_data a b).2.1 (gcd_data a b).2.2.1
    rw [hxy] at hd
    exact hd
  · intro h
    rcases h with ⟨t, ht⟩
    rcases bezout a b with ⟨u, v, huv⟩
    exists u * t, v * t
    rw [← Int.mul_assoc, ← Int.mul_assoc, ← Int.add_mul, huv, ← ht]

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

theorem solution_shift (a b c x₀ y₀ k : Int)
    (h : a * x₀ + b * y₀ = c) :
    a * (x₀ + k * (b / gcd a b)) + b * (y₀ - k * (a / gcd a b)) = c := by
  /-
  Theorem: From one solution, adding k times b/g to x and subtracting
  k times a/g from y gives another solution, where g is the gcd.
  Proof: Write a=g*A and b=g*B. Then a*B=b*A, since both equal
  g*A*B. The change in a*x+b*y is k*(a*B-b*A)=0. QED
  -/
  have hf := gcd_quotients a b
  have heq : a * (b / gcd a b) = b * (a / gcd a b) := by
    calc
      a * (b / gcd a b) = (gcd a b * (a / gcd a b)) * (b / gcd a b) := by
        exact congrArg (fun t => t * (b / gcd a b)) hf.1
      _ = (gcd a b * (b / gcd a b)) * (a / gcd a b) := by
        rw [Int.mul_right_comm]
      _ = b * (a / gcd a b) := by rw [← hf.2]
  have hk := congrArg (fun t : Int => t * k) heq
  simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at hk ⊢
  omega

theorem solution_next (a b c x₀ y₀ : Int) (h : a * x₀ + b * y₀ = c) :
    a * (x₀ + b / gcd a b) + b * (y₀ - a / gcd a b) = c := by
  /-
  Theorem: Increasing x by b/g and decreasing y by a/g preserves a
  solution. Proof: This is the shift formula with the integer k=1.
  QED
  -/
  have hs := solution_shift a b c x₀ y₀ 1 h
  rw [Int.one_mul, Int.one_mul] at hs
  exact hs

theorem homogeneous_solutions (A B dx dy : Int) (hc : gcd A B = 1)
    (h : A * dx + B * dy = 0) : ∃ k : Int, dx = B * k ∧ dy = -(A * k) := by
  /-
  Theorem: If A and B are relatively prime, every solution of
  A*dx+B*dy=0 has the form dx=B*k and dy=-A*k.
  Proof: Choose u,v with A*u+B*v=1. Set k=v*dx-u*dy.
  Multiply the identity by dx, and use A*dx=-B*dy, to obtain

    dx = B*v*dx - B*u*dy = B*k.

  Multiplying by dy and making the same substitution gives dy=-A*k.
  This argument includes cases where A or B is zero. QED
  -/
  rcases coprime_bezout A B hc with ⟨u, v, huv⟩
  exists v * dx - u * dy
  have hx := congrArg (fun t : Int => t * dx) huv
  have hy := congrArg (fun t : Int => t * dy) huv
  have hu := congrArg (fun t : Int => t * u) h
  have hv := congrArg (fun t : Int => t * v) h
  dsimp at hx hy hu hv
  constructor <;>
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
      Int.mul_assoc, Int.mul_left_comm, Int.mul_comm, Int.one_mul,
      Int.mul_one, Int.zero_mul, Int.mul_zero] at hx hy hu hv ⊢ <;> omega

theorem all_solutions (a b c x₀ y₀ x y : Int) (hne : a ≠ 0 ∨ b ≠ 0)
    (h₀ : a * x₀ + b * y₀ = c) (h : a * x + b * y = c) :
    ∃ k : Int, x = x₀ + k * (b / gcd a b) ∧ y = y₀ - k * (a / gcd a b) := by
  /-
  Theorem: Every solution comes from a given solution by the shift
  formula. Proof: Put A=a/g and B=b/g, where g is the positive gcd.
  Subtract the two equations and cancel g to get

    A*(x-x₀) + B*(y-y₀) = 0.

  The reduced coefficients are relatively prime. The homogeneous
  result gives x-x₀=B*k and y-y₀=-A*k. Rearranging yields exactly
  the two claimed formulas. QED
  -/
  have hf := gcd_quotients a b
  have hp := gcd_positive a b hne
  have hh : (a / gcd a b) * (x - x₀) + (b / gcd a b) * (y - y₀) = 0 := by
    apply Int.eq_of_mul_eq_mul_left (a := gcd a b) (by omega)
    rw [Int.mul_add, ← Int.mul_assoc, ← hf.1, ← Int.mul_assoc, ← hf.2,
      Int.mul_zero, Int.mul_sub, Int.mul_sub]
    omega
  rcases homogeneous_solutions (a / gcd a b) (b / gcd a b) (x - x₀) (y - y₀)
    (reduced_coprime a b hne) hh with ⟨k, hkx, hky⟩
  exists k
  rw [Int.mul_comm (b / gcd a b) k] at hkx
  rw [Int.mul_comm (a / gcd a b) k] at hky
  constructor <;> omega

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

theorem gcd_scale (a b : Int) (k : Nat) (hk : 0 < k) (hne : a ≠ 0 ∨ b ≠ 0) :
    gcd ((k : Int) * a) ((k : Int) * b) = (k : Int) * gcd a b := by
  /-
  Theorem: Multiplying both inputs by a positive natural number k
  multiplies the gcd by k. Proof: Write g=gcd(a,b). The number k*g
  is positive and divides both k*a and k*b. If a*x+b*y=g, then

    (k*a)*x + (k*b)*y = k*g.

  The preceding characterization identifies k*g as the new gcd. QED
  -/
  have hg := gcd_data a b
  apply gcd_eq_of_combination ((k : Int) * a) ((k : Int) * b) ((k : Int) * gcd a b)
  · exact Int.mul_pos (by omega) (gcd_positive a b hne)
  · rcases hg.2.1 with ⟨u, hu⟩
    exists u
    exact (congrArg (fun t : Int => (k : Int) * t) hu).trans (Int.mul_assoc _ _ _).symm
  · rcases hg.2.2.1 with ⟨v, hv⟩
    exists v
    exact (congrArg (fun t : Int => (k : Int) * t) hv).trans (Int.mul_assoc _ _ _).symm
  · rcases bezout a b with ⟨x, y, hxy⟩
    exists x, y
    rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_add, hxy]

end NumberTheory.CommonDivisors
