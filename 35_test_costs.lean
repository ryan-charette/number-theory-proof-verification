import «15_reduced_residues»

namespace NumberTheory.TestCosts

/-- A positive natural number has d decimal digits. -/
def DecimalDigits (n d : Nat) : Prop :=
  0<d ∧ 10^(d-1)≤n ∧ n<10^d

/-- A full trial scan tests the integers 2 through the square-root cutoff. -/
def trialCount (cutoff : Nat) : Nat := cutoff-1

theorem trial_count_bounds (n d cutoff : Nat) (hn : 2≤n)
    (hd : DecimalDigits n d)
    (hlower : cutoff*cutoff≤n) (hupper : n<(cutoff+1)*(cutoff+1)) :
    10^(d-1)<(trialCount cutoff+2)*(trialCount cutoff+2) ∧
    (trialCount cutoff+1)*(trialCount cutoff+1)<10^d := by
  /-
  Theorem: For a d-digit input, the full trial-division count T has
  10^(d-1)<(T+2)^2 and (T+1)^2<10^d. These exact bounds place T
  between 10^((d-1)/2)-2 and 10^(d/2)-1, explaining the square-root
  exponential estimate in the number of digits.

  Proof: Let t be the integer cutoff characterized by t^2<=n<(t+1)^2.
  Since n>=2, t>=1. Testing each integer 2,...,t takes T=t-1 trials,
  so T+1=t and T+2=t+1. The decimal bounds give

    10^(d-1) <= n < (t+1)^2,
    t^2 <= n < 10^d.

  Substitution gives both conclusions. This counts the full scan of
  integer candidates. A scan stopping at a factor may take fewer
  trials, and testing primes alone is a different counting model. QED
  -/
  obtain ⟨_,hdecimalLower,hdecimalUpper⟩ := hd
  have ht : 0<cutoff := by
    by_cases hz : cutoff=0
    · simp only [hz,Nat.zero_add,Nat.one_mul] at hupper
      omega
    · omega
  have hcount : trialCount cutoff+1=cutoff := by unfold trialCount; omega
  have hnext : trialCount cutoff+2=cutoff+1 := by omega
  constructor
  · rw [hnext]
    exact Nat.lt_of_le_of_lt hdecimalLower hupper
  · rw [hcount]
    exact Nat.lt_of_le_of_lt hlower hdecimalUpper

end NumberTheory.TestCosts
