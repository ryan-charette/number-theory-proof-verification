import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.DivisorCounts

def positiveRange (n : Nat) : List Nat := (List.range n).map (fun i => i+1)

theorem positive_range_mem (n k : Nat) : k ∈ positiveRange n ↔ 0 < k ∧ k ≤ n := by
  /-
  Lemma: The positive range lists exactly the integers from one to n.
  Proof: Its entries are j+1 for 0≤j<n. Subtracting one gives the
  reverse correspondence. QED
  -/
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j,hj,hjk⟩
    have := List.mem_range.mp hj
    omega
  · intro h
    exact List.mem_map.mpr ⟨k-1,List.mem_range.mpr (by omega),by omega⟩

end NumberTheory.DivisorCounts
