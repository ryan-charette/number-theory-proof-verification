import «33_pell_existence»

namespace NumberTheory.PellPowers

open NumberTheory.SquareParameters NumberTheory.PellProducts NumberTheory.PellExistence

/-- The real value associated with two integer coordinates. -/
noncomputable def value (N : ℕ) (r s : ℤ) : ℝ :=
  (r:ℝ)+(s:ℝ)*Real.sqrt N

def Represents (N : ℕ) (z : ℝ) : Prop :=
  ∃ r s : ℤ, PellSolution N r s ∧ z=value N r s

theorem product_represents {N : ℕ} {z w : ℝ}
    (hz : Represents N z) (hw : Represents N w) : Represents N (z*w) := by
  /-
  Multiply the two expressions r+s√N and a+b√N. The terms without
  a square root add to ra+Nsb, and the coefficient of √N is rb+sa.
  The earlier multiplication formula for integer Pell solutions says
  exactly that these two coefficients solve the equation. QED
  -/
  obtain ⟨r,s,hrs,rfl⟩ := hz
  obtain ⟨a,b,hab,rfl⟩ := hw
  refine ⟨_,_,multiply_solutions N r s a b hrs hab,?_⟩
  unfold value
  push_cast
  have hs := Real.sq_sqrt (show (0:ℝ)≤N by positivity)
  nlinarith only [congrArg (fun t : ℝ => (s:ℝ)*(b:ℝ)*t) hs]

theorem inverse_solution {N : ℕ} {r s : ℤ} (h : PellSolution N r s) :
    (value N r s)⁻¹=value N r (-s) ∧ PellSolution N r (-s) := by
  /-
  Change the sign of s. Its square stays the same, so the new pair
  still solves the Pell equation. Multiplying r+s√N by r-s√N gives
  r²-Ns²=1. Thus the second value is the reciprocal of the first. QED
  -/
  change r*r-(N:ℤ)*(s*s)=1 at h
  have he : (r:ℝ)*(r:ℝ)-(N:ℝ)*((s:ℝ)*(s:ℝ))=1 := by exact_mod_cast h
  have hs := Real.sq_sqrt (show (0:ℝ)≤N by positivity)
  have hp : value N r s * value N r (-s)=1 := by
    unfold value
    push_cast
    nlinarith only [he,congrArg (fun t : ℝ => (s:ℝ)^2*t) hs]
  constructor
  · exact inv_eq_of_mul_eq_one_right hp
  · simpa [PellSolution] using h

theorem integer_power_represents {N : ℕ} {z : ℝ} (hz : Represents N z)
    (k : ℤ) : Represents N (z^k) := by
  /-
  The zeroth power is one, represented by (1,0). For a natural
  exponent, each next power is the previous one times z, so induction
  and the product formula supply integer coordinates. A negative power
  is the reciprocal of the corresponding positive power, for which
  the reciprocal formula supplies coordinates. QED
  -/
  have powers (n : ℕ) : Represents N (z^n) := by
    induction n with
    | zero => exact ⟨1,0,by simp [PellSolution],by simp [value]⟩
    | succ n ih => simpa only [pow_succ] using product_represents ih hz
  cases k with
  | ofNat n => simpa using powers n
  | negSucc n =>
    obtain ⟨r,s,hrs,he⟩ := powers (n+1)
    obtain ⟨hinv,hpair⟩ := inverse_solution hrs
    refine ⟨r,-s,hpair,?_⟩
    simpa only [zpow_negSucc,he] using hinv

end NumberTheory.PellPowers
