import «30_approximations»
import «32_pell_products»

namespace NumberTheory.PellExistence

open NumberTheory.RationalApproximations NumberTheory.SquareParameters

theorem approximation_sum_bound (N x y : ℕ) (hN : 0<N) (hy : 0<y)
    (he : |(x:ℝ)-(y:ℝ)*Real.sqrt N| < 1/(y:ℝ)) :
    (x:ℝ)+(y:ℝ)*Real.sqrt N < 3*(y:ℝ)*Real.sqrt N := by
  /-
  Theorem: A multiple approximation with error less than 1/y satisfies
  x+y*sqrt(N)<3*y*sqrt(N). Proof: N>=1 gives sqrt(N)>=1, and y>=1
  gives 1/y<=1<=y*sqrt(N). The error bound gives x<y*sqrt(N)+1/y.
  Adding y*sqrt(N) proves the claim. N and y are explicitly positive;
  the argument even permits x=0. QED
  -/
  have hyR : (1:ℝ)≤y := by exact_mod_cast hy
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hs0 := Real.sqrt_nonneg (N:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤N by positivity)
  have hs1 : 1≤Real.sqrt (N:ℝ) := by nlinarith
  have hi : 1/(y:ℝ)≤1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hyR
  have hu := (abs_lt.mp he).2
  nlinarith

theorem approximation_norm_bound (N x y : ℕ) (hN : 0<N) (hx : 0<x) (hy : 0<y)
    (he : |(x:ℝ)-(y:ℝ)*Real.sqrt N| < 1/(y:ℝ)) :
    |(x:ℝ)^2-(N:ℝ)*(y:ℝ)^2| < 3*Real.sqrt N := by
  /-
  Theorem: The integer expression x*x-N*y*y associated with a good
  approximation has absolute value less than 3*sqrt(N). Proof: Factor
  it as (x-y*sqrt(N))(x+y*sqrt(N)). The second factor is positive and
  less than 3*y*sqrt(N), by the preceding bound. Taking absolute values
  and multiplying the two bounds gives (1/y)*(3*y*sqrt(N))=3*sqrt(N).
  This bound is independent of x and y. QED
  -/
  have hyR : (0:ℝ)<y := by exact_mod_cast hy
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤N by positivity)
  have hsum := approximation_sum_bound N x y hN hy he
  have hpos : (0:ℝ)<(x:ℝ)+(y:ℝ)*Real.sqrt N := by positivity
  have hid : (x:ℝ)^2-(N:ℝ)*(y:ℝ)^2 =
      ((x:ℝ)-(y:ℝ)*Real.sqrt N)*((x:ℝ)+(y:ℝ)*Real.sqrt N) := by
    nlinarith only [hs2]
  rw [hid,abs_mul,abs_of_pos hpos]
  calc
    _ < (1/(y:ℝ))*((x:ℝ)+(y:ℝ)*Real.sqrt N) :=
      mul_lt_mul_of_pos_right he hpos
    _ < (1/(y:ℝ))*(3*(y:ℝ)*Real.sqrt N) :=
      mul_lt_mul_of_pos_left hsum (one_div_pos.mpr hyR)
    _ = 3*Real.sqrt N := by field_simp; ring
end NumberTheory.PellExistence
