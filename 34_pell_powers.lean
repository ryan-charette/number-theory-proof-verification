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

end NumberTheory.PellPowers
