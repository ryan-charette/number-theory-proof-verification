-- This module serves as the root of the `«Number Theory»` library.
-- Import modules here that should be built as part of the library.
import «Number Theory».Basic
import Mathlib.Tactic.NthRewrite

/-
-- We will prove 2 + 2 = 4 using the Peano Axioms. Lean is powerful enough to
recognize that this is true by basic arithmetic. These sorts of low-level
equalities are automatically handled by rfl. That is,

example : (2 : Nat) + 2 = 4 := by
  rfl

will solve the goal. For pedadagogical purposes, we will pretend that this is
not the case, and will build up to this result from first principles.
-/

/-
rfl proves goals of the form X = X.

Example: 37 * x + q = 37 * x + q
Proof: This is true by the reflexive property of equality
-/
example (x q : Nat) : 37 * x + q = 37 * x + q := by
  rfl

/-
If h is a proof of an equality X = Y, then rw [h] will change all Xs in the
goal to Ys. It's the way to "substitute in".

Example: If y = x + 7, then 2 * y = 2 * (x + 7)
Proof: This is true by substiting y for x + 7 to get 2 * (x + 7) = 2 * (x + 7)
-/
example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
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

/-
We can use rw to rewrite multiple things in one line. We can also reference
any theorems that we have previously proven.

Nat.succ n = n + 1, but we're going to pretend that addition isn't defined yet,
and that the successor function is given to us by the Peano Axioms.

Example: 2 = S(S(0))
Proof: 2 = S(1) = S(S(0)).
-/
example : 2 = Nat.succ (Nat.succ 0) := by
  rw [two_eq_succ_one, one_eq_succ_zero]

/-
If h is a proof of an equality X = Y, then rw [← h] will change all Ys in the
goal to Xs. Type \l to get ← .

Example: 2 = S(S(0))
Proof: S(S(0)) = S(1) = 2. Note the difference compared to the previous example.
-/
example : 2 = Nat.succ (Nat.succ 0) := by
  rw [← one_eq_succ_zero, two_eq_succ_one]

/-
repeat will repeatedly apply a tactic until it no longer succeeds.

Nat.add_zero replaces n + 0 with n. Note that we do not have the commutative
property of addition; this function will not replace 0 + n with n.

Example: a + (b + 0) + (c + 0) = a + b + c
Proof: a + (b + 0) + (c + 0) = a + b + (c + 0) = a + b + c
-/
example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [Nat.add_zero]

/-
Nat.succ_eq_add_one is the built-in method for this.

Theorem: For all n ∈ ℕ, S(n) = n + 1.
Proof: n + 1 = n + S(0) = S(n + 0) = S(n)
-/
theorem succ_eq_add_one n : Nat.succ n = n + 1 := by
  rw[one_eq_succ_zero, Nat.add_succ, Nat.add_zero]

/-
nth_rewrite i j will rewrite only the ith and jth occurrence of the expression
to be rewritten. Indexing starts at 1.

Example: 2 + 2 = 4
Proof: 2 + 2 = 2 + S(1) = S(2 + 1) = S(2 + S(0)) = S(S(2 + 0)) = S(S(2)) = S(3) = 4
-/
example : (2 : Nat) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rw [Nat.add_succ, one_eq_succ_zero, Nat.add_succ, Nat.add_zero, ← three_eq_succ_two, ← four_eq_succ_three]

/-
induction allows us to perform a proof by induction on n. This splits up into
the base case "zero" corresponding to n = 0 and the inductive case "succ"
corresponding to d → d + 1, in which we prove the inductive hypothesis ih.

Theorem: For all n ∈ ℕ, 0 + n = n
Proof: We perform induction on n.
Base case: 0 + 0 = 0 is true by the identity property of addition.
Inductive case: Assume that 0 + d = d. We must show that 0 + S(d) = S(d).
This is true because 0 + S(d) = S(0 + d) = S(d).
-/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, ih]

/-
Theorem: For all a, b ∈ ℕ, S(a) + b = S(a + b)
Proof: We perform induction on b.
Base case: S(a) + 0 = S(a) = S(a + 0)
Inductive case: Assume that S(a) + d = S(a + d). We must show that
S(a) + S(d) = S(a + S(d)). This is true because
S(a) + S(d) = S(S(a) + d) = S(S(a + d)) = S(a + S(d)).
-/
theorem succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero =>
    repeat rw [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, ih, Nat.add_succ]
