import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Lean.Elab.Tactic.Omega

/-
We describe division by an equation m = n * q + r, where n is positive
and 0 ≤ r < n. The integers q and r are the quotient and remainder.
For integers, r < n is equivalent to r ≤ n - 1.

We use well-ordering to find a remainder, then prove uniqueness by
comparing two such equations. No division or remainder operation is
used to obtain the results. The tactic `omega` only checks the indicated
linear inequalities and arithmetic equalities after the main steps.
-/

namespace NumberTheory.Remainders

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

theorem division_exists_unique (m n : Nat) (hn : 0 < n) :
    ∃ q r : Int, (m : Int) = (n : Int) * q + r ∧ 0 ≤ r ∧ r < (n : Int) ∧
      ∀ q' r' : Int, (m : Int) = (n : Int) * q' + r' →
        0 ≤ r' → r' < (n : Int) → q' = q ∧ r' = r := by
  /-
  Theorem: Dividing a natural number by a positive natural number
  gives exactly one quotient and remainder with 0 ≤ r < n.
  Proof: The existence theorem supplies q and r with the equation
  and bounds. If q' and r' also satisfy them, the uniqueness theorem
  gives q' = q and r' = r. This proves both parts of the assertion. QED
  -/
  rcases division_exists m n hn with ⟨q, r, heq, hr, hrn⟩
  exists q, r
  refine ⟨heq, hr, hrn, ?_⟩
  intro q' r' heq' hr' hrn'
  exact division_unique m n q' r' q r (by omega) heq' heq hr' hrn' hr hrn

/-
For a positive modulus n, congruence means divisibility of a - b by n.
We give the definition here so this file can be used on its own.
-/
def Congruent (a b n : Int) : Prop := 0 < n ∧ n ∣ a - b

theorem congruent_iff_equal_remainders (a b n qa ra qb rb : Int)
    (hn : 0 < n) (ha : a = n * qa + ra) (hb : b = n * qb + rb)
    (hra : 0 ≤ ra) (hran : ra < n) (hrb : 0 ≤ rb) (hrbn : rb < n) :
    Congruent a b n ↔ ra = rb := by
  /-
  Theorem: Given quotient-and-remainder decompositions of integers
  a and b with positive divisor n, they are congruent modulo n if
  and only if their remainders are equal. The supplied decompositions
  allow the statement to cover negative integers as well.

  Proof: We prove the two implications separately.

  Forward implication: Suppose a and b are congruent. Then
  a - b = n * k for some integer k. Using b = n * qb + rb gives

    a = b + n * k = n * (qb + k) + rb.

  Thus a has two valid decompositions: the given one with remainder
  ra, and this one with remainder rb. Uniqueness gives ra = rb.

  Reverse implication: Suppose ra = rb. Subtracting the equations,

    a - b = (n * qa + ra) - (n * qb + ra) = n * (qa - qb).

  The integer qa - qb is a witness that n divides a - b. Since n
  is positive, this says precisely that a and b are congruent. QED
  -/
  constructor
  · intro h
    rcases h.2 with ⟨k, hk⟩
    have ha' : a = n * (qb + k) + rb := by
      rw [Int.mul_add]
      omega
    exact (division_unique a n qa ra (qb + k) rb hn ha ha'
      hra hran hrb hrbn).2
  · intro heq
    constructor
    · exact hn
    · exists qa - qb
      rw [Int.mul_sub]
      omega

end NumberTheory.Remainders
