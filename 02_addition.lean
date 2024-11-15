import «Number Theory».Basic
import Mathlib.Tactic.NthRewrite

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
