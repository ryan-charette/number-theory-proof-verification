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

theorem finite_integer_difference (K : ℕ) (hK : 2≤K) (x : Fin K → ℝ) :
    ∃ i j, i≠j ∧ ∃ n : ℤ, |x i-x j-(n:ℝ)| ≤ 1/(K:ℝ) := by
  /-
  Theorem: Among K real numbers, with K>=2, two differ from an integer
  by at most 1/K. Proof: Suppose all pairs were farther apart modulo
  integers. Subtract the smallest fractional part from every fractional
  part, so the new points start at zero. No point can reach 1-1/K:
  its distance around the end of the unit interval to zero would then
  be at most 1/K. The K points therefore lie in only K-1 half-open
  intervals of length 1/K. Two occupy the same interval, contradicting
  the assumed separation. The restriction K>=2 is necessary for a pair
  of distinct entries to exist. QED
  -/
  classical
  by_contra hn
  have hKR : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have avoid (i j : Fin K) (hij : i≠j) (n : ℤ) :
      1/(K:ℝ)< |x i-x j-(n:ℝ)| := by
    apply lt_of_not_ge
    intro hh
    exact hn ⟨i,j,hij,n,hh⟩
  let i0 : Fin K := ⟨0,by omega⟩
  obtain ⟨m,_hm,hmin⟩ := Finset.exists_min_image Finset.univ (fun i => Int.fract (x i))
    ⟨i0,by simp⟩
  let d (i : Fin K) := Int.fract (x i)-Int.fract (x m)
  have dnon (i : Fin K) : 0≤d i := sub_nonneg.mpr (hmin i (by simp))
  have dlt (i : Fin K) : d i<1-1/(K:ℝ) := by
    by_cases him : i=m
    · subst i
      have htwo : (2:ℝ)≤K := by exact_mod_cast hK
      have hinv := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) htwo
      dsimp only [d]
      linarith
    · have hh := avoid i m him (⌊x i⌋-⌊x m⌋+1)
      have hid : x i-x m-((⌊x i⌋-⌊x m⌋+1:ℤ):ℝ)=d i-1 := by
        simp only [d,Int.fract,Int.cast_add,Int.cast_sub,Int.cast_one]
        ring
      rw [hid] at hh
      have hdi : d i<1 := by
        have := Int.fract_lt_one (x i)
        have := Int.fract_nonneg (x m)
        dsimp only [d]
        linarith
      rw [abs_of_neg (by linarith : d i-1<0)] at hh
      linarith
  have hmul (i : Fin K) : (K:ℝ)*d i<(K-1:ℕ) := by
    have hh := mul_lt_mul_of_pos_left (dlt i) hKR
    have hid : (K:ℝ)*(1-1/(K:ℝ))=(K:ℝ)-1 := by field_simp
    rw [hid] at hh
    rw [Nat.cast_sub (by omega : 1≤K),Nat.cast_one]
    exact hh
  let box (i : Fin K) : Fin (K-1) := ⟨⌊(K:ℝ)*d i⌋₊,
    (Nat.floor_lt (mul_nonneg hKR.le (dnon i))).mpr (hmul i)⟩
  obtain ⟨i,j,hij,hbox⟩ := Fintype.exists_ne_map_eq_of_card_lt box (by simp; omega)
  have hf : ⌊(K:ℝ)*d i⌋₊=⌊(K:ℝ)*d j⌋₊ := congrArg Fin.val hbox
  have hi := Nat.floor_le (mul_nonneg hKR.le (dnon i))
  have hj := Nat.floor_le (mul_nonneg hKR.le (dnon j))
  have hi' := Nat.lt_floor_add_one ((K:ℝ)*d i)
  have hj' := Nat.lt_floor_add_one ((K:ℝ)*d j)
  rw [hf] at hi hi'
  have hd : |d i-d j|<1/(K:ℝ) := by
    apply abs_lt.mpr
    constructor
    · have hh : -(1:ℝ)<(d i-d j)*(K:ℝ) := by nlinarith
      simpa only [neg_div] using (div_lt_iff hKR).mpr hh
    · apply (lt_div_iff hKR).mpr
      nlinarith
  have hid : x i-x j-((⌊x i⌋-⌊x j⌋:ℤ):ℝ)=d i-d j := by
    simp only [d,Int.fract,Int.cast_sub]
    ring
  have hh := avoid i j hij (⌊x i⌋-⌊x j⌋)
  rw [hid] at hh
  linarith

theorem bounded_denominator (α : ℝ) (K : ℕ) (hK : 0<K) :
    ∃ p : ℤ, ∃ q : ℕ, 0<q ∧ q≤K ∧ |(q:ℝ)*α-(p:ℝ)| < 1/(K:ℝ) ∧
      (0≤α → 0≤p ∧ (p:ℝ)≤(K:ℝ)*α) := by
  /-
  Lemma: There are integers p and 1<=q<=K for which |q*alpha-p|<1/K.
  Proof: Apply the fractional-part pigeonhole lemma to the multiples
  0,alpha,...,K*alpha. Order the two selected indices i<j. Put q=j-i
  and p=floor(j*alpha)-floor(i*alpha). Subtracting the two fractional
  parts gives q*alpha-p exactly. The indices give the stated bounds
  on q. For nonnegative alpha, monotonicity of the floor makes p
  nonnegative, and p<=floor(j*alpha)<=K*alpha. QED
  -/
  obtain ⟨i,j,hne,hh⟩ := fractional_collision K hK (fun i => (i.val:ℝ)*α)
  have ordered (i j : Fin (K+1)) (hlt : i.val<j.val)
      (hh : |Int.fract ((i.val:ℝ)*α)-Int.fract ((j.val:ℝ)*α)| < 1/(K:ℝ)) :
      ∃ p : ℤ, ∃ q : ℕ, 0<q ∧ q≤K ∧ |(q:ℝ)*α-(p:ℝ)| < 1/(K:ℝ) ∧
      (0≤α → 0≤p ∧ (p:ℝ)≤(K:ℝ)*α) := by
    refine ⟨⌊(j.val:ℝ)*α⌋-⌊(i.val:ℝ)*α⌋, j.val-i.val, by omega, by omega, ?_, ?_⟩
    · have hid : ((j.val-i.val:ℕ):ℝ)*α-
          ((⌊(j.val:ℝ)*α⌋-⌊(i.val:ℝ)*α⌋:ℤ):ℝ) =
          -(Int.fract ((i.val:ℝ)*α)-Int.fract ((j.val:ℝ)*α)) := by
        rw [Nat.cast_sub (by omega),Int.cast_sub]
        simp only [Int.fract]
        ring
      rw [hid,abs_neg]
      exact hh
    · intro hα
      have hji : (i.val:ℝ)≤j.val := by exact_mod_cast (Nat.le_of_lt hlt)
      have hp := Int.floor_mono (mul_le_mul_of_nonneg_right hji hα)
      have hfi : (0:ℤ)≤⌊(i.val:ℝ)*α⌋ := Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hα)
      have hfj := Int.floor_le ((j.val:ℝ)*α)
      have hfiR : (0:ℝ)≤(⌊(i.val:ℝ)*α⌋:ℝ) := by exact_mod_cast hfi
      have hjK : (j.val:ℝ)≤K := by exact_mod_cast (show j.val≤K by omega)
      have hbound := mul_le_mul_of_nonneg_right hjK hα
      refine ⟨sub_nonneg.mpr hp,?_⟩
      rw [Int.cast_sub]
      linarith
  by_cases hij : i.val<j.val
  · exact ordered i j hij hh
  · have hji : j.val<i.val := by
      have hval : i.val≠j.val := fun h => hne (Fin.ext h)
      omega
    apply ordered j i hji
    rwa [abs_sub_comm]

theorem scaled_approximation_iff (α : ℝ) (p : ℤ) (q : ℕ) (hq : 0<q) :
    |(p:ℝ)/(q:ℝ)-α| ≤ 1/(q:ℝ)^2 ↔ |(p:ℝ)-(q:ℝ)*α| ≤ 1/(q:ℝ) := by
  /-
  Lemma: The fraction-error and multiple-error bounds are equivalent.
  Proof: Subtract alpha from p/q over the common denominator q.
  Absolute values divide by q since it is positive. Multiplication
  by q changes 1/q^2 into 1/q and preserves the inequality. QED
  -/
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hid : (p:ℝ)/(q:ℝ)-α=((p:ℝ)-(q:ℝ)*α)/(q:ℝ) := by field_simp
  have hb : 1/(q:ℝ)^2*(q:ℝ)=1/(q:ℝ) := by field_simp; ring
  rw [hid,abs_div,abs_of_pos hqR,div_le_iff₀ hqR,hb]

theorem finite_multiple_approximation (α : ℝ) (hα : 0<α) (K : ℕ) (hK : 0<K) :
    ∃ a b : ℕ, ∃ c : ℤ, a<b ∧ b≤K ∧ 0≤c ∧ (c:ℝ)≤(K:ℝ)*α ∧
      |(c:ℝ)/((b-a:ℕ):ℝ)-α| ≤ 1/((b-a:ℕ):ℝ)^2 := by
  /-
  Theorem: A positive input has a finite multiple approximation with
  0<=a<b<=K and 0<=c<=K*alpha and the quadratic error bound.
  Proof: The pigeonhole construction gives q<=K and an integer c
  between zero and K*alpha with |q*alpha-c|<1/K<=1/q. Divide by q
  and take a=0,b=q. Zero is explicitly allowed for a and c, as the
  displayed bounds require; demanding positivity would fail for small
  K and alpha. The construction also works for rational inputs. QED
  -/
  obtain ⟨c,q,hq,hqK,he,hc⟩ := bounded_denominator α K hK
  refine ⟨0,q,c,hq,hqK,(hc hα.le).1,(hc hα.le).2,?_⟩
  simp only [Nat.sub_zero]
  apply (scaled_approximation_iff α c q hq).mpr
  rw [abs_sub_comm]
  exact le_trans he.le (one_div_le_one_div_of_le (by exact_mod_cast hq) (by exact_mod_cast hqK))

end NumberTheory.RationalApproximations
