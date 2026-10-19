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

theorem positive_range_nodup (n : Nat) : (positiveRange n).Nodup := by
  /-
  Lemma: The positive range has no repetitions.
  Proof: Adding one to two different natural numbers cannot make
  them equal; the original range has no repetitions. QED
  -/
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp (R := fun i j : Nat => i ≠ j) ?_ (List.nodup_range n)
  intro i j h he
  exact h (by omega)

def divisors (n : Nat) : List Nat := (positiveRange n).filter (fun d => decide (d ∣ n))

theorem divisors_mem (n d : Nat) (hn : 0 < n) :
    d ∈ divisors n ↔ 0 < d ∧ d ∣ n := by
  /-
  Lemma: Our divisor list contains precisely the positive divisors.
  Proof: A positive divisor of positive n is at most n, so filtering
  the interval from one to n loses no divisor. QED
  -/
  simp only [divisors,List.mem_filter,decide_eq_true_eq,positive_range_mem]
  constructor
  · intro h; exact ⟨h.1.1,h.2⟩
  · intro h; exact ⟨⟨h.1,Nat.le_of_dvd hn h.2⟩,h.2⟩

theorem divisors_nodup (n : Nat) : (divisors n).Nodup := by
  /-
  Lemma: Each divisor is listed only once.
  Proof: Filtering a list without repetitions cannot introduce one.
  QED
  -/
  exact (positive_range_nodup n).filter _

theorem divisor_factor (n d : Nat) (hn : 0 < n) (hd : d ∣ n) :
    0 < n/d ∧ (n/d)*d=n := by
  /-
  Lemma: For a divisor d of positive n, the complementary factor
  n/d is positive and its product with d is n. Proof: Exact integer
  division gives the product identity. A zero quotient would force
  n=0, contrary to its positivity. QED
  -/
  have he := Nat.div_mul_cancel hd
  refine ⟨?_,he⟩
  by_cases hz : n/d=0
  · rw [hz,Nat.zero_mul] at he; omega
  · exact Nat.pos_of_ne_zero hz

end NumberTheory.DivisorCounts
