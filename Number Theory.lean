-- This module serves as the root of the `«Number Theory»` library.
-- Import modules here that should be built as part of the library.
import «Number Theory».Basic
import Mathlib.Tactic.NthRewrite

/-
PEANO ARITHMETIC
-/

/-
-- We will prove 2 + 2 = 4 using the Peano Axioms. Lean is powerful enough to
recognize that this is true by basic arithmetic. These sorts of low-level
equalities are automatically handled by `rfl`. That is,

example : (2 : Nat) + 2 = 4 := by
  rfl

will solve the goal. For pedadagogical purposes, we will pretend that this is
not the case, and will build up to this result from first principles. Our main
tool in this section will be `rw` and related rewrite commands.
-/

example (x q : Nat) : 37 * x + q = 37 * x + q := by
  /-
  `rfl` proves goals of the form X = X.

  Example: 37 * x + q = 37 * x + q
  Proof: This is true by the reflexive property of equality. QED
  -/
  rfl

example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  /-
  If `h` is a proof of an equality X = Y, then `rw [h]` will change all X's in
  the goal to Y's. It's the way to "substitute in".

  Example: If y = x + 7, then 2 * y = 2 * (x + 7)
  Proof: Substitute y for x + 7 and use the reflexivity of equality:

  2 * y = 2 * (x + 7)

  2 * (x + 7) = 2 * x + 7    [Substituting y = x + 7]

  QED
  -/
  rw [h]

/-
Here we are defining 1 := S(0), 2 := S(1), 3 := S(2), and 4 := S(3), where S(n)
denotes the successor of n.
-/
theorem one_eq_succ_zero : 1 = Nat.succ 0 := by
  rfl
theorem two_eq_succ_one : 2 = Nat.succ 1 := by
  rfl
theorem three_eq_succ_two : 3 = Nat.succ 2 := by
  rfl
theorem four_eq_succ_three : 4 = Nat.succ 3 := by
  rfl

example : 2 = Nat.succ (Nat.succ 0) := by
  /-
  We can use `rw` to rewrite multiple things in one line. We can also reference
  any theorems that we have previously proven.

  `Nat.succ n` = n + 1, but we're going to pretend that addition isn't defined
  yet, and that the successor function is given to us by the Peano Axioms.

  Example: 2 = S(S(0))
  Proof: This follows from our definitions of 1 and 2:

  2 = S(S(0))

  S(1) = S(S(0))    [Definition of 2]

  S(S(S(0))         [Definition of 1]

  QED
  -/
  rw [two_eq_succ_one, one_eq_succ_zero]

example : 2 = Nat.succ (Nat.succ 0) := by
  /-
  If `h` is a proof of an equality X = Y, then `rw [← h]` will change all Y's
  in the goal to X's. Type \l to get ←.

  Example: 2 = S(S(0))
  Proof: This follows from our definitions of 1 and 2. Note the difference
  compared to the previous example:

  2 = S(S(0))

  2 = S(1)    [Definition of 1]

  2 = 2       [Definition of 2]

  QED
  -/
  rw [← one_eq_succ_zero, ← two_eq_succ_one]

example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  /-
  repeat will repeatedly apply a tactic until it no longer succeeds.

  `Nat.add_zero` replaces n + 0 with n. Note that we do not have the
  commutative property of addition; it will not replace 0 + n with n.
  This function represents Peano's first axiom of addition, which states that
  for all n ∈ ℕ, n + 0 = n

  Example: a + (b + 0) + (c + 0) = a + b + c
  Proof: Apply Peano's first axiom of addition to both b + 0 and c + 0:

  a + (b + 0) + (c + 0) = a + b + c

  a + b + c = a + b + c    [Apply Peano's first axiom of addition twice:
                           We rewrite b + 0 = b and c + 0 = c in one step]

  QED
  -/
  repeat rw [Nat.add_zero]

theorem succ_eq_add_one n : Nat.succ n = n + 1 := by
  /-
  Theorem: For all n ∈ ℕ, S(n) = n + 1.
  Proof: We will need Peano's second axiom of addition, which states that for
  all n ∈ ℕ, n + S(0) = S(n + 0):

  S(n) = n + 1

  S(n) = n + S(0)    [Definition of 1]

  S(n) = S(n + 0)    [Peano's second axiom of addition]

  S(n) = S(n)        [Peano's first axiom of addition]

  QED
  -/
  rw[one_eq_succ_zero, Nat.add_succ, Nat.add_zero]

example : (2 : Nat) + 2 = 4 := by
  /-
  `nth_rewrite i j` will rewrite only the `i`th and `j`th occurrence of the
  expression to be rewritten. Indexing starts at 1.

  Example: 2 + 2 = 4
  Proof: This follows directly from definitions and Peano's axioms of addition:

  2 + 2 = 4

  2 + S(1) = 4       [Definition of 2]

  S(2 + 1) = 4       [Peano's second axiom of addition]

  S(2 + S(0)) = 4    [Definition of 1]

  S(S(2 + 0)) = 4    [Peano's second axiom of addition]

  S(S(2)) = 4        [Peano's first axiom of addition]

  S(3) = 4           [Definition of 3]

  4 = 4              [Definition of 4]

  QED
  -/
  nth_rewrite 2 [two_eq_succ_one]
  rw [Nat.add_succ, one_eq_succ_zero, Nat.add_succ, Nat.add_zero,
  ← three_eq_succ_two, ← four_eq_succ_three]

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


/-
DIVISIBILITY AND CONGRUENCE
-/

theorem dvd_add (a b c : Int) (h₀ : a ∣ b) (h₁ : a ∣ c) : a ∣ (b + c) := by
  /-
  Theorem: If a ∣ b and a ∣ c, then a ∣ (b + c)
  Proof:

  h₀ : a ∣ b             [True by hypothesis]
  h₁ : a ∣ c

  hₖ : ∃k : a * k = b    [Definition of divisible]
  hₗ : ∃l : a * l = c

  a ∣ (b + c)

  a ∣ (a * k + a * l)    [Substitution via `hk` and `hl`]

  a ∣ a * (k + l)        [Factor out the `a` term]
  -/
  rcases h₀ with ⟨k, hk⟩
  rcases h₁ with ⟨l, hl⟩
  rw [hk, hl, ← Int.mul_add]
  exists (k + l)
