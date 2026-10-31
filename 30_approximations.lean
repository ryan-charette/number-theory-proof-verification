import «05_divisibility_tests»
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace NumberTheory.RationalApproximations

theorem fixed_denominator (α : ℝ) (b : ℕ) (hb : 0<b) :
    ∃ a : ℤ, |α-(a:ℝ)/(b:ℝ)| ≤ 1/(2*(b:ℝ)) := by
  /-
  Theorem: For any prescribed positive denominator b, a fraction a/b
  lies within 1/(2b) of the given real number.
  Proof: Let a be the floor of b*alpha+1/2. The defining floor bounds
  give -1/2 <= b*alpha-a < 1/2. Dividing by the positive number b
  gives the desired distance bound. This argument works for every
  real input, so it also proves the statement for irrational inputs. QED
  -/
  let a : ℤ := Int.floor ((b:ℝ)*α+1/2)
  have hlow := Int.floor_le ((b:ℝ)*α+1/2)
  have hupp := Int.lt_floor_add_one ((b:ℝ)*α+1/2)
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have ha : |(b:ℝ)*α-(a:ℝ)| ≤ (1:ℝ)/2 := by
    apply abs_le.mpr
    dsimp [a]
    constructor <;> linarith
  refine ⟨a,?_⟩
  have hid : α-(a:ℝ)/(b:ℝ)=((b:ℝ)*α-(a:ℝ))/(b:ℝ) := by
    field_simp
    ring
  rw [hid,abs_div,abs_of_pos hbR]
  apply (div_le_iff₀ hbR).mpr
  calc
    |(b:ℝ)*α-(a:ℝ)| ≤ 1/2 := ha
    _ = 1/(2*(b:ℝ))*(b:ℝ) := by field_simp

end NumberTheory.RationalApproximations
