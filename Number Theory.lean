-- This module serves as the root of the `«Number Theory»` library.
-- Import modules here that should be built as part of the library.

/-
Our next goal is to prove the commutativity of addition (i.e, a + b = b + a).
We won't need to introduce any new definitions of axioms to prove this result,
but several lemmas are necessary. Unlike our previous result, `rfl` is not
powerful enough to solve this automatically. That is,

theorem add_comm (a b : Nat) : a + b = b + a := by
  rfl

does not solve the goal. The main tool that we introduce in this section is
`induction`.
-/

theorem zero_add (n : Nat) : 0 + n = n := by
  /-
  `induction` allows us to perform a proof by induction on n. This splits up
  into the base case `zero` for n = 0 and the inductive case `succ` for
  d → d + 1, where we prove the inductive hypothesis `ih`.

  Theorem: For all n ∈ ℕ, 0 + n = n
  Proof: We perform induction on n.

  Base case:

    0 + 0 = 0

    0 = 0    [Peano's first axiom of addition]

  Inductive case: Assume that 0 + d = d for some d ∈ ℕ.

    0 + S(d) = S(d)

    S(0 + d) = S(d)    [Peano's second axiom of addition]

    S(d) = S(d)        [By the inductive hypothesis]

  QED
  -/
  induction n with
  | zero =>
    rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, ih]

theorem succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  /-
  Theorem: For all a, b ∈ ℕ, S(a) + b = S(a + b)
  Proof: We perform induction on b.

  Base case:

    S(a) + 0 = S(a + 0)

    S(a) = S(a)    [Apply Peano's first axiom of addition on both sides]

  Inductive case: Assume that S(a) + d = S(a + d) for some d ∈ ℕ.

    S(a) + S(d) = S(a + S(d))

    S(S(a) + d) = S(a + S(d))    [Peano's second axiom of addition]

    S(S(a + d)) = S(a + S(d))    [The inductive hypothesis]

    S(S(a + d)) = S(S(a + d))    [Peano's second axiom of addition]

  QED
  -/
  induction b with
  | zero =>
    repeat rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, ih, Nat.add_succ]

theorem add_comm (a b : Nat) : a + b = b + a := by
  /-
  Theorem: Addition of natural numbers is commutative. That is, for all
  a, b ∈ ℕ, a + b = b + a.
  Proof: We perform induction on a.

  Base case:

    0 + b = b + 0

    0 + b = b    [Peano's first axiom of addition]

    b = b        [Apply the `zero_add` theorem]

  Inductive case: Assume that d + b = b + d for some d ∈ ℕ.

    S(d) + b = b + S(d)

    S(d) + b = S(b + d)    [Peano's second axiom of addition]

    S(d + b) = S(b + d)    [Apply the `succ_add` theorem]

    S(b + d) = S(b + d)    [The inductive hypothesis]

  QED
  -/
  induction a with
  | zero =>
    rw [Nat.add_zero, Nat.zero_add]
  | succ d ih =>
    /-
    rw [← Nat.succ_eq_add_one] is needed because Lean uses d + 1 rather than
    S(d) for the inductive case.
    -/
    rw [← Nat.succ_eq_add_one, Nat.add_succ, Nat.succ_add, ih]

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  /-
  Theorem: Addition of natural numbers is associative. That is, for all
  a, b, c ∈ ℕ, (a + b) + c = a + (b + c).
  Proof: We perform induction on a.

  Base case:

    (0 + b) + c = 0 + (b + c)

    b + c = b + c    [Apply the `zero_add` theorem to both sides]

  Inductive case: Assume that (d + b) + c = d + (b + c) for some d ∈ ℕ.

    (S(d) + b) + c = S(d) + (b + c)

    S((d + b) + c) = S(d + (b + c))    [Apply Peano's second axiom of addition
                                       to both sides]

    S(d + (b + c)) = S(d + (b + c))    [The inductive hypothesis]

  QED
  -/
  induction a with
  | zero =>
    repeat rw [Nat.zero_add]
  | succ d ih =>
    rw [← Nat.succ_eq_add_one]
    repeat rw [Nat.succ_add]
    rw [ih]

theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b := by
  /-
  If the goal is a + b + c = a + c + b then rw [add_comm b c] will not work
  because there is no b + c term in the goal (a + b) + c = (a + c) + b.

  Theorem: a + b + c = a + c + b
  Proof:

  a + b + c = a + c + b

  a + (b + c) = a + (c + b)    [Associative property of addition (`add_comm`)]

  a + (b + c) = a + (c + b)    [Commutative property of addition (`add_assoc`)]

  QED
  -/
  repeat rw [Nat.add_assoc]
  rw [Nat.add_comm b]

theorem mul_one (m : Nat) : m * 1 = m := by
  /-
  Theorem: m * 1 = m
  Proof:

  m * 1 = m

  m * succ(0) = m    [Definition of 1]

  m * 0 + m = m      [Definition of multiplication of successors]

  0 + m = m          [Definition of multiplication by zero]

  m = m              [Zero sum property (`zero_add`)]

  QED
  -/
  rw [one_eq_succ_zero, Nat.mul_succ, Nat.mul_zero, Nat.zero_add]

theorem zero_mul (m : Nat) : 0 * m = 0 := by
  /-
  Theorem: 0 * m = 0
  Proof: We perform induction on m.

  Base Case:

    0 * 0 = 0

    0 = 0    [Zero product property of right-multiplication (`mul_zero`)]

  Inductive Case:

    0 * succ(d) = 0

    0 * d + 0 = 0    [Defintion of multiplication]

    0 + 0 = 0        [Inductive hypothesis]

    0 = 0            [Zero sum property (`add_zero`)]

  QED
  -/
  induction m with
  | zero =>
    rw [Nat.mul_zero]
  | succ d ih =>
    rw [Nat.mul_succ, ih, Nat.add_zero]

theorem succ_mul (a b : Nat) : Nat.succ a * b = a * b + b := by
  /-
  Theorem: S(a) * b = a * b + b
  Proof: We perform induction on b.

  Base Case:

    S(a) * 0 = a * 0 + 0

    0 = 0 + 0    [Zero product property]

    0 = 0        [Zero sum property]

  Inductive Case:

    S(a) * S(d) = a * S(d) + S(d)

    S(a) * d + S(a) = a * d + a + S(d)          [Definition of multiplication]

    S(a) * d + (a + 1) = a * d + a + (d + 1)    [Definition of succ]

    S(a) * d + a + 1 = a * d + a + d + 1        [Associativity of addition]

    a * d + d + a + 1 = a * d + a + d + 1       [Inductive hypothesis]

    a * d + a + d + 1 = a * d + a + d + 1       [Commutativity of addition]

  QED
  -/
  induction b with
  | zero =>
    rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  | succ d ih =>
    repeat rw[Nat.mul_succ]
    repeat nth_rewrite 2 [Nat.succ_eq_add_one]
    repeat rw [← add_assoc]
    rw [ih]
    nth_rewrite 2 [Nat.add_right_comm]
    rfl

theorem mul_comm (a b : Nat) : a * b = b * a := by
  /-
  Theorem: Multplication of natural numbers is commutative. That is, for all
  a, b ∈ ℕ, a * b = b * a.
  Proof: We perform induction on a.

  Base case:

    0 * b = b * 0

    0 * b = b    [Definition of multiplication]

    b = b        [Apply the `zero_mul` theorem]

  Inductive case: Assume that d * b = b * d for some d ∈ ℕ.

    S(d) * b = b * S(d)

    S(d) * b = S(b * d)    [Definition of multiplication]

    S(d * b) = S(b * d)    [Apply the `succ_mul` theorem]

    S(b * d) = S(b * d)    [The inductive hypothesis]

  QED
  -/
  induction a with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_mul]
  | succ d ih =>
    /-
    rw [← Nat.succ_eq_add_one] is needed because Lean uses d + 1 rather than
    S(d) for the inductive case.
    -/
    rw [← Nat.succ_eq_add_one, Nat.mul_succ, Nat.succ_mul, ih]

theorem one_mul (m : Nat): 1 * m = m := by
  /-
  Theorem: 1 * m = m
  Proof:

  1 * m = m

  m * 1 = m    [Commutative property of multiplication (`mul_comm`)]

  m = m        [Apply the `mul_one` theorem]

  QED
  -/
  rw [mul_comm, mul_one]

theorem two_mul (m : Nat): 2 * m = m + m := by
  /-
  Theorem: 2 * m = m + m
  Proof:

  2 * m = m + m

  S(1) * m = m + m     [Definition of 2]

  1 * m + m = m + m    [Definition of multiplication]

  m + m = m + m        [Apply the `one_mul` theorem]

  QED
  -/
  rw [two_eq_succ_one, Nat.succ_mul, Nat.one_mul]

theorem mul_add(a b c : Nat): a * (b + c) = a * b + a * c := by
  /-
  Theorem: a * (b + c) = a * b + a * c
  Proof: We use induction on c.

  Base Case:

    a * (b + 0) = a * b + a * 0

    a * b = a * b + a * 0    [1st Addition Axiom]

    a * b = a * b + 0        [Definition of Multiplication]

    a * b = a * b            [1st Addition Axiom]

  Inductive Case:

    a * (b + S(d)) = a * b + a * S(d)

    a * (S(b + d)) = a * b + a * S(d)            [2nd Addition Axiom]

    a * (b + d) + a = a * b + a * S(d)           [Definition of mulitiplication]

    a * b + a * d + a = a * b + a * S(d)         [Inductive hypothesis]

    a * b + a * d + a = a * b + (a * d + a)      [Definition of multiplication]

    a * b + (a * d + a) = a * b + (a * d + a)    [Associativity of addition]

  QED
  -/
  induction c with
  | zero =>
    rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, Nat.mul_succ, ih, Nat.mul_succ, Nat.add_assoc]

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  /-
  Theorem: (a + b) * c = a * c + b * c
  Proof:

  (a + b) * c = a * c + b * c

  c * (a + b) = a * c + b * c      [Commutativity of multiplicaiton]

  c * a + c * b = a * c + b * c    [Left-distributivity of multiplication]

  a * c + b * c = a * c + b * c    [Commutativity of multiplicaiton]
  -/
  rw [mul_comm, mul_add]
  repeat rw [mul_comm c]

theorem mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction a with
  | zero =>
    repeat rw [zero_mul]
  | succ d ih =>
    rw [succ_mul, succ_mul, add_mul, ih]
