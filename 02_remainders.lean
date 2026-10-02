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

end NumberTheory.Remainders
