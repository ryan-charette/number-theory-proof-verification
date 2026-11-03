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
theorem recurring_label {α : Type} (labels : List α) (f : ℕ → α)
    (hf : ∀ i, f i ∈ labels) :
    ∃ k ∈ labels, ∀ B : ℕ, ∃ i, B<i ∧ f i=k := by
  /-
  Lemma: A sequence taking only finitely many labels has a label that
  occurs at arbitrarily large indices. Proof: Induct on the list of
  labels. The empty list cannot contain even the first value. For a
  nonempty list, either its first label recurs arbitrarily late, or
  there is a bound after which it never occurs. In the latter case,
  discard that initial segment and apply induction to the remaining
  labels. An arbitrarily late index in the shifted sequence is also
  arbitrarily late in the original one. QED
  -/
  classical
  induction labels generalizing f with
  | nil => simpa using hf 0
  | cons k ks ih =>
    by_cases hk : ∀ B : ℕ, ∃ i, B<i ∧ f i=k
    · exact ⟨k,by simp,hk⟩
    · push_neg at hk
      obtain ⟨B,hB⟩ := hk
      have ht : ∀ i, f (i+B+1) ∈ ks := by
        intro i
        have hh := hf (i+B+1)
        rcases List.mem_cons.mp hh with hh|hh
        · exact False.elim (hB (i+B+1) (by omega) hh)
        · exact hh
      obtain ⟨l,hl,hi⟩ := ih (fun i => f (i+B+1)) ht
      refine ⟨l,List.mem_cons_of_mem k hl,?_⟩
      intro C
      obtain ⟨i,hi,he⟩ := hi C
      exact ⟨i+B+1,by omega,he⟩

end NumberTheory.PellExistence
