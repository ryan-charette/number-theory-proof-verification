import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.SquareClasses

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

theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The gcd of two integers is an integer linear combination.
  Proof: These are the coefficients constructed by the Euclidean
  procedure and back-substitution above. The construction also covers
  the harmless extra case a = b = 0. QED
  -/
  exact (gcd_data a b).2.2.2

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

def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d=1 ∨ d=p

theorem prime_coprime (a : Int) (p : Nat) (hp : Prime p) (ha : ¬ (p : Int) ∣ a) :
    gcd a p=1 := by
  /-
  Lemma: An integer not divisible by a prime is relatively prime
  to it. Proof: The positive gcd d divides p, so primality makes
  d either one or p. The latter would imply p divides a, which
  is excluded. Hence d=1. QED
  -/
  have hd := gcd_positive a p (Or.inr (by have := hp.1; omega))
  have hcast := Int.toNat_of_nonneg (Int.le_of_lt hd)
  have hdiv : (gcd a p).toNat ∣ p := by
    apply Int.ofNat_dvd.mp
    rw [hcast]
    exact (gcd_data a p).2.2.1
  rcases hp.2 _ hdiv with h | h
  · omega
  · have he : gcd a p=(p : Int) := by omega
    have had := (gcd_data a p).2.1
    rw [he] at had
    exact False.elim (ha had)

def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a-b

local notation:50 a " ≡ " b " [MOD " n "]" => Congruent a b n

theorem inverse_integer (a : Int) (p : Nat) (hp : Prime p)
    (ha : ¬ (p : Int) ∣ a) : ∃ u : Int, Congruent (a*u) 1 p := by
  /-
  Lemma: An integer not divisible by a prime has an inverse modulo
  that prime. Proof: Bezout gives a*u+p*v=1, since their gcd is one.
  Thus a*u-1=p*(-v), which proves the required congruence. QED
  -/
  rcases bezout a p with ⟨u,v,h⟩
  rw [prime_coprime a p hp ha] at h
  refine ⟨u,by have := hp.1; omega,-v,?_⟩
  rw [Int.mul_neg]
  omega

theorem dvd_mult_of_dvd_left (a b c : Int) (h : a ∣ b) : a ∣ b * c := by
  /-
  Theorem: If a divides b, then a divides b * c for any integer c.
  Proof: If b = a * m, then

    b * c = (a * m) * c = a * (m * c).

  Use m * c as the witness. QED
  -/
  rcases h with ⟨m, hm⟩
  exists m * c
  rw [hm, Int.mul_assoc]

theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ b + c := by
  /-
  Theorem: A common divisor divides the sum.
  Proof: Write b = a * m and c = a * n. Then

    b + c = a * m + a * n    [Substitution]
          = a * (m + n)      [Distributivity]

  The integer m + n is the required witness. QED
  -/
  rcases h₀ with ⟨m, hm⟩
  rcases h₁ with ⟨n, hn⟩
  exists m + n
  rw [hm, hn, Int.mul_add]

theorem modeq_mult (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] := by
  /-
  Theorem: Congruences can be multiplied.
  Proof: We must show that n divides a * c - b * d. We can express
  this difference in terms of a - b and c - d:

    a * c - b * d = a * c - b * c + b * c - b * d
                 = (a - b) * c + b * (c - d).

  Since n divides a - b, it divides (a - b) * c. Similarly, since n
  divides c - d, it divides b * (c - d). It therefore divides their
  sum, which is a * c - b * d. QED
  -/
  constructor
  · exact h₀.1
  · have h₂ := dvd_mult_of_dvd_left n (a - b) c h₀.2
    have h₃ := dvd_mult_of_dvd_left n (c - d) b h₁.2
    have h := dvd_add n ((a - b) * c) ((c - d) * b) h₂ h₃
    rw [Int.mul_comm (c - d) b, Int.sub_mul, Int.mul_sub,
      ← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem modeq_refl (a n : Int) (hn : 0 < n) : a ≡ a [MOD n] := by
  /-
  Theorem: Every integer is congruent to itself.
  Proof: The modulus n is positive by hypothesis. Also,

    a - a = 0 = n * 0.

  Thus n divides a - a, using the integer 0. QED
  -/
  constructor
  · exact hn
  · exists 0
    rw [Int.sub_self, Int.mul_zero]

theorem modeq_add (a b c d n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  /-
  Theorem: Congruences can be added.
  Proof: We must show that n divides (a + c) - (b + d).
  Rearranging the additions and subtractions gives

    (a + c) - (b + d) = (a - b) + (c - d).

  By hypothesis, n divides each term on the right. Our theorem on
  divisibility of sums shows that n divides the left side as well. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (c - d) h₀.2 h₁.2
    have heq : (a + c) - (b + d) = (a - b) + (c - d) := by
      simp only [Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc]
      rw [Int.add_left_comm c (-b)]
    rw [heq]
    exact h

theorem modeq_trans (a b c n : Int)
    (h₀ : a ≡ b [MOD n]) (h₁ : b ≡ c [MOD n]) : a ≡ c [MOD n] := by
  /-
  Theorem: Two consecutive congruences combine.
  Proof: The hypotheses tell us that n divides a - b and b - c.
  Therefore n divides their sum. Adding the differences gives:

    (a - b) + (b - c) = a - c.

  Both differences are divisible by n, so their sum is too. QED
  -/
  constructor
  · exact h₀.1
  · have h := dvd_add n (a - b) (b - c) h₀.2 h₁.2
    rw [← Int.add_sub_assoc, Int.sub_add_cancel] at h
    exact h

theorem cancel_coprime (a b c n : Int) (hcop : gcd c n=1)
    (h : Congruent (a*c) (b*c) n) : Congruent a b n := by
  /-
  Theorem: A factor relatively prime to the modulus can be cancelled
  from a congruence.
  Proof: Write (a-b)*c=n*q and c*u+n*v=1. Multiplying the latter
  identity by a-b and substituting the former gives
  a-b=n*(q*u+(a-b)*v). This witness proves the desired congruence.
  QED
  -/
  rcases bezout c n with ⟨u,v,he⟩
  rw [hcop] at he
  rcases h.2 with ⟨q,hq⟩
  have hd : (a-b)*c=n*q := by rw [Int.sub_mul]; exact hq
  refine ⟨h.1,q*u+(a-b)*v,?_⟩
  calc
    a-b = (a-b)*1 := by rw [Int.mul_one]
    _ = (a-b)*(c*u+n*v) := congrArg (fun z => (a-b)*z) he.symm
    _ = ((a-b)*c)*u+n*((a-b)*v) := by
      rw [Int.mul_add,←Int.mul_assoc,Int.mul_left_comm (a-b) n v]
    _ = n*(q*u+(a-b)*v) := by rw [hd,Int.mul_add,Int.mul_assoc]

theorem modeq_symm (a b n : Int) (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  /-
  Theorem: Reversing a congruence preserves it.
  Proof: By the definition of congruence, n is positive and
  a - b = n * k for some integer k. Then

    b - a = -(a - b) = -(n * k) = n * (-k).

  Use -k as the witness. QED
  -/
  rcases h with ⟨hn, k, hk⟩
  constructor
  · exact hn
  · exists -k
    rw [← Int.neg_sub a b, hk, Int.mul_neg]

theorem monic_quadratic (a b c : Int) (p : Nat) (hp : Prime p)
    (ha : ¬ (p : Int) ∣ a) :
    ∃ b' c' : Int, ∀ x : Int,
      Congruent (a*x^2+b*x+c) 0 p ↔ Congruent (x^2+b'*x+c') 0 p := by
  /-
  Theorem: A quadratic with nonzero leading coefficient modulo a
  prime has the same solutions as a monic quadratic.
  Proof: Choose u with a*u congruent to one and put b'=u*b, c'=u*c.
  Multiplying the monic expression by a gives an expression congruent
  to the original quadratic. Cancellation of the coprime factor a
  shows that one is zero exactly when the other is zero. QED
  -/
  rcases inverse_integer a p hp ha with ⟨u,hu⟩
  have hn : 0 < (p : Int) := by have := hp.1; omega
  refine ⟨u*b,u*c,fun x => ?_⟩
  have hb := modeq_mult (a*u) 1 (b*x) (b*x) p hu (modeq_refl _ _ hn)
  have hc := modeq_mult (a*u) 1 c c p hu (modeq_refl _ _ hn)
  have he := modeq_add _ _ _ _ p (modeq_add _ _ _ _ p
    (modeq_refl (a*x^2) p hn) hb) hc
  simp only [Int.one_mul,Int.mul_assoc] at he
  have he' : Congruent (a*(x^2+(u*b)*x+u*c)) (a*x^2+b*x+c) p := by
    simpa only [Int.mul_add,Int.mul_assoc] using he
  constructor
  · intro h
    have hz := modeq_trans _ _ _ p he' h
    apply cancel_coprime _ 0 a p (prime_coprime a p hp ha)
    simpa only [Int.mul_comm,Int.zero_mul,Int.mul_zero] using hz
  · intro h
    have hz := modeq_mult a a _ 0 p (modeq_refl _ _ hn) h
    simp only [Int.mul_zero] at hz
    exact modeq_trans _ _ _ p (modeq_symm _ _ p he') hz

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

theorem odd_prime_data (p : Nat) (hp : Prime p) (hodd : p % 2=1) :
    0 < (p-1)/2 ∧ p-1=2*((p-1)/2) ∧ ¬ (p : Int) ∣ 2 := by
  /-
  Lemma: For an odd prime, p-1 is twice a positive integer, and
  p does not divide two. Proof: Oddness and p>1 give p>=3.
  Division by two yields p-1=2*((p-1)/2). A positive divisor of
  two is at most two, so p cannot divide two. QED
  -/
  have hp1 := hp.1
  refine ⟨by omega,by omega,?_⟩
  intro h
  have := divisor_le_positive (p : Int) 2 (by omega) h
  omega

theorem complete_square (b c : Int) (p : Nat) (hp : Prime p) (hodd : p % 2=1) :
    ∃ alpha beta : Int, ∀ x : Int,
      Congruent (x^2+b*x+c) 0 p ↔ Congruent ((x+alpha)^2) beta p := by
  /-
  Theorem: Over an odd prime modulus a translation changes a monic
  quadratic equation into a square equation.
  Proof: Invert two modulo p. Choose alpha with 2*alpha congruent
  to b, and put beta=alpha^2-c. Expanding gives
    (x+alpha)^2-beta = x^2+2*alpha*x+c.
  This is congruent to x^2+b*x+c. Hence their being zero is
  equivalent. The odd-prime hypothesis is the approved correction;
  it is needed to invert two. QED
  -/
  rcases inverse_integer 2 p hp (odd_prime_data p hp hodd).2.2 with ⟨u,hu⟩
  have hn : 0 < (p : Int) := by have := hp.1; omega
  let alpha := u*b
  have ha : Congruent (2*alpha) b p := by
    simpa only [alpha,Int.mul_assoc,Int.one_mul] using
      modeq_mult (2*u) 1 b b p hu (modeq_refl _ _ hn)
  refine ⟨alpha,alpha^2-c,fun x => ?_⟩
  have hh := modeq_add _ _ _ _ p
    (modeq_add _ _ _ _ p (modeq_refl (x^2) p hn)
      (modeq_mult _ b x x p ha (modeq_refl _ _ hn)))
    (modeq_refl c p hn)
  have he : (x+alpha)^2-(alpha^2-c)=x^2+(2*alpha)*x+c := by
    simp only [Int.pow_succ,Int.pow_zero,Int.mul_one,Int.one_mul,Int.add_mul,Int.mul_add]
    rw [Int.mul_comm x alpha,Int.mul_assoc 2 alpha x]
    omega
  constructor
  · intro h
    have hz := modeq_trans _ _ _ p hh h
    refine ⟨hn,?_⟩
    rw [he]
    simpa only [Int.sub_zero] using hz.2
  · intro h
    have hz : Congruent (x^2+(2*alpha)*x+c) 0 p := by
      refine ⟨hn,?_⟩
      simpa only [he,Int.sub_zero] using h.2
    exact modeq_trans _ _ _ p (modeq_symm _ _ p hh) hz

def SquareClass (a : Int) (p : Nat) : Prop := ∃ x : Int, Congruent (x^2) a p

theorem square_class_congruent (a b : Int) (p : Nat) (h : Congruent a b p) :
    SquareClass a p ↔ SquareClass b p := by
  /-
  Lemma: Congruent integers are either both squares or both nonsquares.
  Proof: A square congruent to one is congruent to the other by
  transitivity. Use the reverse congruence for the converse. QED
  -/
  constructor
  · rintro ⟨x,hx⟩; exact ⟨x,modeq_trans _ _ _ p hx h⟩
  · rintro ⟨x,hx⟩; exact ⟨x,modeq_trans _ _ _ p hx (modeq_symm _ _ p h)⟩

theorem gcd_one_right (a n : Int) (hn : 0 < n)
    (h : ∃ u v : Int, a*u+n*v=1) : gcd a n=1 := by
  /-
  Lemma: A positive modulus n and a linear combination a*u+n*v=1
  imply gcd(a,n)=1, even when a is zero or negative.
  Proof: The positive gcd divides this linear combination, so it
  divides one and is at most one. Positivity makes it exactly one.
  QED
  -/
  rcases h with ⟨u,v,he⟩
  have hd := dvd_linear (gcd a n) a n u v
    (gcd_data a n).2.1 (gcd_data a n).2.2.1
  rw [he] at hd
  have hle := divisor_le_positive (gcd a n) 1 (by decide) hd
  have hp := gcd_positive a n (Or.inr (by omega))
  omega

theorem congruent_coprime (a b n : Int) (hcop : gcd a n=1)
    (h : Congruent a b n) : gcd b n=1 := by
  /-
  Theorem: Replacing a number by a congruent integer preserves
  coprimality with the modulus.
  Proof: Write a-b=n*q and a*u+n*v=1. Substitution gives
  b*u+n*(q*u+v)=1. This is a Bezout identity for b and n,
  so their gcd is one. QED
  -/
  rcases bezout a n with ⟨u,v,he⟩
  rw [hcop] at he
  rcases h.2 with ⟨q,hq⟩
  apply gcd_one_right b n h.1
  refine ⟨u,q*u+v,?_⟩
  have ht := congrArg (fun z => z*u) hq
  change (a-b)*u=(n*q)*u at ht
  rw [Int.sub_mul,Int.mul_assoc] at ht
  rw [Int.mul_add]
  omega

theorem gcd_one_combination (a n : Int) (h : ∃ u v : Int, a*u+n*v=1) : gcd a n=1 := by
  /-
  Lemma: A linear combination equal to one forces the gcd to be
  one, without any sign restriction on either input. Proof: The
  nonnegative gcd divides the combination one. It cannot be zero,
  and a divisor of one is at most one, so it equals one. QED
  -/
  rcases h with ⟨u,v,he⟩
  have hd := dvd_linear (gcd a n) a n u v (gcd_data a n).2.1 (gcd_data a n).2.2.1
  rw [he] at hd
  have hb := divisor_le_positive (gcd a n) 1 (by decide) hd
  have hp := (gcd_data a n).1
  have hz : gcd a n ≠ 0 := by
    intro hzero
    rcases hd with ⟨k,hk⟩
    rw [hzero,Int.zero_mul] at hk
    omega
  omega

theorem bezout_product (a b c : Int)
    (hb : ∃ u v : Int, a*u+b*v=1) (hc : ∃ u v : Int, a*u+c*v=1) :
    ∃ u v : Int, a*u+(b*c)*v=1 := by
  /-
  Lemma: If a has a linear combination equal to one with each of
  b and c, it also has one with b*c.
  Proof: Write a*u+b*v=1 and a*p+c*q=1. Multiply the second
  equality by b*v and substitute for b*v in the first. We obtain
  a*(u+b*v*p)+(b*c)*(v*q)=1. These are the required coefficients.
  QED
  -/
  rcases hb with ⟨u,v,hu⟩
  rcases hc with ⟨p,q,hp⟩
  refine ⟨u+b*v*p,v*q,?_⟩
  have he := congrArg (fun t => t*(b*v)) hp
  simp only [Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_assoc,
    Int.mul_left_comm,Int.mul_comm,Int.mul_one] at he ⊢
  omega

theorem coprime_product_iff (a m n : Int) :
    gcd a (m*n)=1 ↔ gcd a m=1 ∧ gcd a n=1 := by
  /-
  Lemma: An integer is coprime to a product exactly when it is
  coprime to each factor.
  Proof: A Bezout identity a*u+(m*n)*v=1 is also an identity for
  a,m and for a,n, by regrouping the second term. Conversely,
  combining identities for a,m and a,n gives one for a,m*n.
  The Bezout characterization proves both directions. QED
  -/
  constructor
  · intro hc
    rcases bezout a (m*n) with ⟨u,v,he⟩
    rw [hc] at he
    constructor
    · apply gcd_one_combination a m
      exact ⟨u,n*v,by simpa only [Int.mul_assoc] using he⟩
    · apply gcd_one_combination a n
      exact ⟨u,m*v,by simpa only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using he⟩
  · rintro ⟨hm,hn⟩
    rcases bezout a m with ⟨u,v,hu⟩
    rcases bezout a n with ⟨s,t,hs⟩
    rw [hm] at hu
    rw [hn] at hs
    exact gcd_one_combination a (m*n) (bezout_product a m n ⟨u,v,hu⟩ ⟨s,t,hs⟩)

theorem coprime_power_iff (a m : Int) (k : Nat) :
    gcd a (m^(k+1))=1 ↔ gcd a m=1 := by
  /-
  Lemma: Coprimality to a positive power is equivalent to
  coprimality to its base.
  Proof: The first power is the base. For the induction step,
  split m^(k+2) into m^(k+1)*m. Coprimality to this product is
  equivalent to coprimality to both factors, which by induction
  is just the single condition for m. QED
  -/
  induction k with
  | zero => simp only [Nat.zero_add,Int.pow_succ,Int.pow_zero,Int.one_mul]
  | succ k ih =>
    rw [Int.pow_succ,coprime_product_iff,ih]
    exact ⟨fun h => h.1,fun h => ⟨h,h⟩⟩

theorem root_is_coprime (x b : Int) (n k : Nat) (hk : 0 < k)
    (hb : gcd b n=1) (h : Congruent (x^k) b n) : gcd x n=1 := by
  /-
  Lemma: A positive-power root of a coprime residue is coprime
  to the modulus. Proof: Congruence makes x^k coprime whenever
  b is coprime. Coprimality to a positive power is equivalent to
  coprimality to the base, using the product criterion. QED
  -/
  have hc := congruent_coprime b (x^k) n hb (modeq_symm _ _ n h)
  -- Reverse the inputs using their Bezout identity.
  have hswap : gcd (n : Int) (x^k)=1 := by
    rcases bezout (x^k) n with ⟨s,t,he⟩
    rw [hc] at he
    exact gcd_one_combination n (x^k) ⟨t,s,by omega⟩
  have he : k=(k-1)+1 := by omega
  rw [he] at hswap
  have hc' := (coprime_power_iff n x (k-1)).mp hswap
  rcases bezout (n : Int) x with ⟨s,t,hs⟩
  rw [hc'] at hs
  exact gcd_one_combination x n ⟨t,s,by omega⟩

def intProduct : List Int → Int
  | [] => 1
  | a::xs => a*intProduct xs

theorem product_congruent (xs : List Nat) (f g : Nat → Int) (n : Int) (hn : 0 < n)
    (h : ∀ i ∈ xs, Congruent (f i) (g i) n) :
    Congruent (intProduct (xs.map f)) (intProduct (xs.map g)) n := by
  /-
  Lemma: Products of corresponding congruent factors are congruent.
  Proof: Induct on the list. Empty products are both one. For a
  nonempty list multiply the head congruence by the congruence
  of the remaining products supplied by induction. QED
  -/
  induction xs with
  | nil => exact modeq_refl 1 n hn
  | cons i xs ih =>
    exact modeq_mult _ _ _ _ n (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem integer_division_exists (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ q r : Int, a=(n : Int)*q+r ∧ 0 ≤ r ∧ r < n := by
  /-
  Lemma: Every integer has a quotient and a nonnegative remainder
  less than a positive natural divisor n.
  Proof: Let t=|a|. Since n≥1, a+n*t≥a+|a|≥0. Divide this
  nonnegative integer by n using the well-ordering construction.
  If a+n*t=n*q+r, then a=n*(q-t)+r, with the same remainder bounds.
  QED
  -/
  let t : Int := a.natAbs
  have ht : 0 ≤ t := by dsimp [t]; omega
  have ha : -a ≤ t := by
    have h : -a ≤ (-a).natAbs := Int.le_natAbs
    simpa only [Int.natAbs_neg] using h
  have hmul := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ n) ht
  rw [Int.one_mul] at hmul
  have hnonneg : 0 ≤ a+(n : Int)*t := by omega
  rcases division_exists (a+(n : Int)*t).toNat n hn with ⟨q,r,he,hr,hrn⟩
  rw [Int.toNat_of_nonneg hnonneg] at he
  refine ⟨q-t,r,?_,hr,hrn⟩
  rw [Int.mul_sub]
  omega

theorem division_unique (m n q r q' r' : Int) (hn : 0 < n)
    (h : m = n * q + r) (h' : m = n * q' + r')
    (hr : 0 ≤ r) (hrn : r < n) (hr' : 0 ≤ r') (hrn' : r' < n) :
    q = q' ∧ r = r' := by
  /-
  Theorem: Two decompositions with the same positive divisor and
  remainders between zero and n - 1 have equal quotients and remainders.
  We allow any integer m, which also covers natural-number dividends.

  Proof: Suppose m = n * q + r = n * q' + r'. If q < q', the
  quotients are integers, so q + 1 ≤ q'. Multiplying by positive n,

    n * q + n ≤ n * q'.

  But r < n and r' ≥ 0 give

    m = n * q + r < n * q + n ≤ n * q' ≤ n * q' + r' = m.

  This is impossible. Interchanging the two decompositions rules out
  q' < q in exactly the same way. Therefore q = q'. Substituting into
  the original equations and cancelling n * q gives r = r'. QED
  -/
  have hnot : ¬ q < q' := by
    intro hlt
    have hstep : q + 1 ≤ q' := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left hstep (Int.le_of_lt hn)
    rw [Int.mul_add, Int.mul_one] at hmul
    -- The remainder bounds would force m < m.
    omega
  have hnot' : ¬ q' < q := by
    intro hlt
    have hstep : q' + 1 ≤ q := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left hstep (Int.le_of_lt hn)
    rw [Int.mul_add, Int.mul_one] at hmul
    omega
  have hq : q = q' := by omega
  constructor
  · exact hq
  · rw [hq] at h
    omega

theorem bounded_congruent_equal (r s m : Int) (hr : 0 ≤ r) (hrm : r < m)
    (hs : 0 ≤ s) (hsm : s < m) (h : r ≡ s [MOD m]) : r=s := by
  /-
  Lemma: Two congruent integers between zero and m-1 are equal.
  Proof: Write r-s=m*q. Then r=m*q+s and also r=m*0+r.
  Both remainders satisfy the required bounds, so uniqueness of
  quotient and remainder makes r=s. QED
  -/
  rcases h.2 with ⟨q,hq⟩
  exact (division_unique r m 0 r q s h.1 (by simp) (by omega)
    hr hrm hs hsm).2

theorem canonical_residue (a : Int) (n : Nat) (hn : 0 < n) :
    ∃ r : Int, 0 ≤ r ∧ r < n ∧ a ≡ r [MOD (n : Int)] ∧
      ∀ s : Int, 0 ≤ s → s < n → a ≡ s [MOD (n : Int)] → s=r := by
  /-
  Theorem: Every integer is congruent to exactly one integer among
  zero through n-1, for positive n.
  Proof: Division gives a=n*q+r with 0≤r<n, so a-r=n*q proves
  congruence. If s is another such representative, reverse the
  congruence a≡s and combine it with a≡r to get s≡r. Bounded
  congruent representatives are equal. QED
  -/
  rcases integer_division_exists a n hn with ⟨q,r,he,hr,hrn⟩
  have hcong : a ≡ r [MOD (n : Int)] := ⟨by omega,q,by omega⟩
  refine ⟨r,hr,hrn,hcong,?_⟩
  intro s hs hsn hsc
  exact bounded_congruent_equal s r n hs hsn hr hrn
    (modeq_trans s a r n (modeq_symm a s n hsc) hcong)

noncomputable def canonicalLabel (a : Int) (n : Nat) : Nat :=
  if h : 0 < n then (Classical.choose (canonical_residue a n h)).toNat else 0

theorem canonicalLabel_spec (a : Int) (n : Nat) (hn : 0 < n) :
    canonicalLabel a n < n ∧ a ≡ (canonicalLabel a n : Int) [MOD (n : Int)] := by
  /-
  Lemma: The canonical label is less than n and represents its input.
  Proof: Choose the unique representative already proved to exist.
  It is nonnegative, so conversion to a natural number preserves its
  value and both stated properties. At modulus zero the definition
  is total by convention, but the lemma requires positive modulus.
  QED
  -/
  have h := Classical.choose_spec (canonical_residue a n hn)
  have hcast := Int.toNat_of_nonneg h.1
  unfold canonicalLabel
  rw [dif_pos hn]
  constructor
  · omega
  · rw [Int.toNat_of_nonneg h.1]
    exact h.2.2.1

theorem product_perm (xs ys : List Int) (h : xs.Perm ys) : intProduct xs=intProduct ys := by
  /-
  Lemma: Rearranging a finite list preserves its product.
  Proof: The elementary rearrangement steps are keeping a common
  head, swapping adjacent entries, and composing rearrangements.
  Induction on these steps uses multiplication's associativity and
  commutativity for a swap, and equality for the other steps. QED
  -/
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [intProduct,ih]
  | swap a b xs => simp only [intProduct,Int.mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem canonicalLabel_eq_iff (a b : Int) (n : Nat) (hn : 0 < n) :
    canonicalLabel a n = canonicalLabel b n ↔ a ≡ b [MOD (n : Int)] := by
  /-
  Lemma: Two inputs have the same canonical label exactly when they
  are congruent. Proof: Equal labels give a common representative;
  transitivity yields congruence of the inputs. Conversely, congruent
  inputs have congruent labels by symmetry and transitivity. Both
  labels lie between zero and n-1, so they are equal. QED
  -/
  have ha := canonicalLabel_spec a n hn
  have hb := canonicalLabel_spec b n hn
  constructor
  · intro he
    have hac := ha.2
    rw [he] at hac
    exact modeq_trans a (canonicalLabel b n) b n hac (modeq_symm b _ n hb.2)
  · intro h
    have hlabels := modeq_trans (canonicalLabel a n) a (canonicalLabel b n) n
      (modeq_symm a _ n ha.2) (modeq_trans a b _ n h hb.2)
    have he := bounded_congruent_equal (canonicalLabel a n) (canonicalLabel b n) n
      (by omega) (by omega) (by omega) (by omega) hlabels
    omega

theorem scaled_labels_injective (a : Int) (n : Nat) (hn : 0 < n) (hc : gcd a n=1)
    (i j : Nat) (hi : i < n) (hj : j < n)
    (he : canonicalLabel ((i : Int)*a) n=canonicalLabel ((j : Int)*a) n) : i=j := by
  /-
  Lemma: Multiplication by a coprime integer gives distinct residue
  labels to distinct canonical representatives. Proof: Equal labels
  give i*a congruent to j*a. Cancel a; the representatives i and j
  lie between zero and n-1, so their congruence makes them equal.
  QED
  -/
  have h := (canonicalLabel_eq_iff _ _ n hn).mp he
  have hcancel := cancel_coprime i j a n hc h
  have hb := bounded_congruent_equal i j n (by omega) (by omega)
    (by omega) (by omega) hcancel
  omega

end NumberTheory.SquareClasses
