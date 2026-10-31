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

theorem fractional_collision (K : ℕ) (hK : 0<K) (x : Fin (K+1) → ℝ) :
    ∃ i j, i≠j ∧ |Int.fract (x i)-Int.fract (x j)| < 1/(K:ℝ) := by
  /-
  Lemma: Among K+1 real numbers two fractional parts differ by less
  than 1/K. Proof: Partition [0,1) into K half-open intervals of length
  1/K. The interval containing a fractional part has index equal to
  the floor of K times that part. Two indices coincide by the finite
  pigeonhole principle. The floor bounds then put the difference
  strictly between -1/K and 1/K. QED
  -/
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  let box (i : Fin (K+1)) : Fin K := ⟨⌊(K:ℝ)*Int.fract (x i)⌋₊, by
    apply (Nat.floor_lt (mul_nonneg hKR.le (Int.fract_nonneg _))).mpr
    nlinarith [Int.fract_lt_one (x i)]⟩
  obtain ⟨i,j,hne,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt box (by simp)
  have hf : ⌊(K:ℝ)*Int.fract (x i)⌋₊ = ⌊(K:ℝ)*Int.fract (x j)⌋₊ := congrArg Fin.val heq
  have hi := Nat.floor_le (mul_nonneg hKR.le (Int.fract_nonneg (x i)))
  have hj := Nat.floor_le (mul_nonneg hKR.le (Int.fract_nonneg (x j)))
  have hi' := Nat.lt_floor_add_one ((K:ℝ)*Int.fract (x i))
  have hj' := Nat.lt_floor_add_one ((K:ℝ)*Int.fract (x j))
  rw [hf] at hi hi'
  refine ⟨i,j,hne,abs_lt.mpr ⟨?_,?_⟩⟩
  · have hh : -(1:ℝ)<(Int.fract (x i)-Int.fract (x j))*(K:ℝ) := by nlinarith
    have := (div_lt_iff hKR).mpr hh
    simpa only [neg_div] using this
  · apply (lt_div_iff hKR).mpr
    nlinarith

end NumberTheory.RationalApproximations
