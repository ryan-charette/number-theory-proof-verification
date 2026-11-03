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

end NumberTheory.PellExistence
