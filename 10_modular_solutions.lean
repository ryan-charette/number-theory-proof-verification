import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ModularSolutions

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

theorem bezout (a b : Int) : ∃ x y : Int, a * x + b * y = gcd a b := by
  /-
  Theorem: The gcd of two integers is an integer linear combination.
  Proof: These are the coefficients constructed by the Euclidean
  procedure and back-substitution above. The construction also covers
  the harmless extra case a = b = 0. QED
  -/
  exact (gcd_data a b).2.2.2

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


def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a-b

theorem linear_congruence_iff_equation (a b n x : Int) (hn : 0 < n) :
    Congruent (a*x) b n ↔ ∃ y : Int, a*x+n*y=b := by
  /-
  Theorem: A solution x of a*x congruent to b modulo n is exactly
  an x that can be extended to a solution of a*x+n*y=b.
  Proof: A congruence gives a*x-b=n*q, so choose y=-q. Conversely,
  a*x+n*y=b gives a*x-b=n*(-y), the divisibility witness. QED
  -/
  constructor
  · rintro ⟨_,q,hq⟩
    exists -q
    rw [Int.mul_neg]
    omega
  · rintro ⟨y,hy⟩
    refine ⟨hn,-y,?_⟩
    rw [Int.mul_neg]
    omega


theorem congruence_solvable_iff (a b n : Int) (hn : 0 < n) :
    (∃ x : Int, Congruent (a*x) b n) ↔ gcd a n ∣ b := by
  /-
  Theorem: The linear congruence a*x congruent to b modulo n has a
  solution exactly when gcd(a,n) divides b.
  Proof: A congruence solution extends to a solution of a*x+n*y=b.
  The integer equation is solvable exactly when its gcd divides b,
  as proved using Bezout coefficients. Conversely, any solution of
  that equation gives a congruence solution by the preceding equivalence.
  QED
  -/
  constructor
  · rintro ⟨x,hx⟩
    rcases (linear_congruence_iff_equation a b n x hn).mp hx with ⟨y,hy⟩
    exact (linear_solvable_iff a n b).mp ⟨x,y,hy⟩
  · intro hd
    rcases (linear_solvable_iff a n b).mpr hd with ⟨x,y,hy⟩
    exact ⟨x,(linear_congruence_iff_equation a b n x hn).mpr ⟨y,hy⟩⟩


theorem modulus_step_data (a n : Int) (hn : 0 < n) :
    0 < gcd a n ∧ 0 < n/gcd a n ∧ n=gcd a n*(n/gcd a n) := by
  /-
  Lemma: For positive n, its gcd d with a is positive, the quotient
  s=n/d is positive, and n=d*s.
  Proof: The inputs are not both zero, so d>0. Divisibility by the
  gcd makes the quotient exact. If s≤0, multiplying by d>0 would
  give n≤0, a contradiction. QED
  -/
  have hd := gcd_positive a n (Or.inr (by omega))
  have he := (gcd_quotients a n).2
  refine ⟨hd,?_,he⟩
  by_cases hs : n/gcd a n ≤ 0
  · have hm := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hd) hs
    rw [←he] at hm
    omega
  · omega


theorem reduced_cross_product (a n : Int) :
    a*(n/gcd a n)=n*(a/gcd a n) := by
  /-
  Lemma: Multiplying a by n/d equals multiplying n by a/d, where
  d=gcd(a,n). Proof: Write a=d*A and n=d*N using exact division.
  Both products are d*A*N, up to reordering the factors. QED
  -/
  have hf := gcd_quotients a n
  calc
    a*(n/gcd a n) = (gcd a n*(a/gcd a n))*(n/gcd a n) :=
      congrArg (fun z => z*(n/gcd a n)) hf.1
    _ = (gcd a n*(n/gcd a n))*(a/gcd a n) := by rw [Int.mul_right_comm]
    _ = n*(a/gcd a n) := congrArg (fun z => z*(a/gcd a n)) hf.2.symm


theorem reduced_modulus_dvd_iff (a n z : Int) (hn : 0 < n) :
    n ∣ a*z ↔ n/gcd a n ∣ z := by
  /-
  Lemma: n divides a*z exactly when n/d divides z, where d=gcd(a,n).
  Proof: Choose a*u+n*v=d. If a*z=n*q, multiplying the Bezout
  equation by z gives d*z=n*(q*u+v*z). Substituting n=d*(n/d)
  and cancelling positive d gives z=(n/d)*(q*u+v*z).
  Conversely, if z=(n/d)*k, the cross-product identity gives
  a*z=n*((a/d)*k), an explicit quotient. QED
  -/
  have hg := modulus_step_data a n hn
  constructor
  · rintro ⟨q,hq⟩
    rcases bezout a n with ⟨u,v,hu⟩
    exists q*u+v*z
    apply Int.eq_of_mul_eq_mul_left (a := gcd a n) (by omega)
    calc
      gcd a n*z = (a*u+n*v)*z := congrArg (fun t => t*z) hu.symm
      _ = (a*z)*u+n*(v*z) := by
        simp only [Int.add_mul,Int.mul_add,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
      _ = n*(q*u+v*z) := by rw [hq,Int.mul_add,Int.mul_assoc]
      _ = gcd a n*((n/gcd a n)*(q*u+v*z)) := by
        calc
          n*(q*u+v*z) = (gcd a n*(n/gcd a n))*(q*u+v*z) :=
            congrArg (fun t => t*(q*u+v*z)) hg.2.2
          _ = _ := by rw [Int.mul_assoc]
  · rintro ⟨k,hk⟩
    exists (a/gcd a n)*k
    calc
      a*z = a*((n/gcd a n)*k) := congrArg (fun t => a*t) hk
      _ = (a*(n/gcd a n))*k := by rw [Int.mul_assoc]
      _ = (n*(a/gcd a n))*k := congrArg (fun t => t*k) (reduced_cross_product a n)
      _ = n*((a/gcd a n)*k) := by rw [Int.mul_assoc]



theorem solution_difference_iff (a b n x₀ x : Int) (hn : 0 < n)
    (h₀ : Congruent (a*x₀) b n) :
    Congruent (a*x) b n ↔ n/gcd a n ∣ x-x₀ := by
  /-
  Theorem: Once x₀ is a solution, x is a solution exactly when
  x-x₀ is divisible by n/gcd(a,n).
  Proof: Subtract the equations a*x-b=n*q and a*x₀-b=n*q₀.
  Their difference says n divides a*(x-x₀). The reduced-modulus
  criterion converts this to divisibility of x-x₀. Conversely,
  that criterion makes a*(x-x₀) a multiple of n; adding the equation
  for x₀ gives an equation proving x is a solution. QED
  -/
  rcases h₀.2 with ⟨q₀,hq₀⟩
  constructor
  · rintro ⟨_,q,hq⟩
    apply (reduced_modulus_dvd_iff a n (x-x₀) hn).mp
    refine ⟨q-q₀,?_⟩
    rw [Int.mul_sub,Int.mul_sub]
    omega
  · intro hd
    rcases (reduced_modulus_dvd_iff a n (x-x₀) hn).mpr hd with ⟨q,hq⟩
    rw [Int.mul_sub] at hq
    refine ⟨hn,q+q₀,?_⟩
    rw [Int.mul_add]
    omega

end NumberTheory.ModularSolutions
