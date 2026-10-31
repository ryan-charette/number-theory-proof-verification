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

/-- Irrationality means inequality with every fraction having positive denominator. -/
def Irrational (α : ℝ) : Prop :=
  ∀ a : ℤ, ∀ b : ℕ, 0<b → α ≠ (a:ℝ)/(b:ℝ)

theorem multiple_separation (α : ℝ) (hi : Irrational α) (q : ℕ) (hq : 0<q) :
    ∃ ε : ℝ, 0<ε ∧ ∀ p : ℤ, ε ≤ |(q:ℝ)*α-(p:ℝ)| := by
  /-
  Lemma: A fixed positive multiple of an irrational number stays a
  positive distance from every integer. Proof: Its fractional part t
  is strictly between zero and one; equality with zero would express
  alpha as a fraction. Take epsilon=min(t,1-t). An integer at or below
  the floor is at least t away; an integer above the floor is at least
  1-t away. QED
  -/
  let t := Int.fract ((q:ℝ)*α)
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have ht0 : 0<t := by
    have hnon := Int.fract_nonneg ((q:ℝ)*α)
    have hne : t≠0 := by
      intro hh
      apply hi ⌊(q:ℝ)*α⌋ q hq
      apply (eq_div_iff (ne_of_gt hqR)).mpr
      dsimp only [t,Int.fract] at hh
      nlinarith
    exact lt_of_le_of_ne hnon (Ne.symm hne)
  have ht1 : t<1 := Int.fract_lt_one _
  refine ⟨min t (1-t),lt_min ht0 (by linarith),?_⟩
  intro p
  by_cases hp : p≤⌊(q:ℝ)*α⌋
  · have hpR : (p:ℝ)≤(⌊(q:ℝ)*α⌋:ℝ) := by exact_mod_cast hp
    have ht : t≤(q:ℝ)*α-(p:ℝ) := by dsimp only [t,Int.fract]; linarith
    exact le_trans (min_le_left _ _) (le_trans ht (le_abs_self _))
  · have hpR : (⌊(q:ℝ)*α⌋:ℝ)+1≤(p:ℝ) := by exact_mod_cast (show ⌊(q:ℝ)*α⌋+1≤p by omega)
    have ht : 1-t≤-((q:ℝ)*α-(p:ℝ)) := by dsimp only [t,Int.fract]; linarith
    exact le_trans (min_le_right _ _) (le_trans ht (neg_le_abs _))

theorem unbounded_denominators (α : ℝ) (hi : Irrational α) (B : ℕ) :
    ∃ p : ℤ, ∃ q : ℕ, B<q ∧ |(q:ℝ)*α-(p:ℝ)| < 1/(q:ℝ) := by
  /-
  Theorem: Irrational inputs have approximations with arbitrarily large
  positive denominators and |q*alpha-p|<1/q. Proof: For each positive
  q<=B choose the positive distance from its multiple to the integers;
  for q=0 assign distance one. The minimum of this finite collection
  is positive. Choose K with 1/K below that minimum, and use the
  bounded-denominator approximation. Its denominator cannot be at
  most B. Since q<=K, its error is also less than 1/q. QED
  -/
  classical
  have hex (i : Fin (B+1)) : ∃ ε : ℝ, 0<ε ∧
      (0<i.val → ∀ p : ℤ, ε≤|(i.val:ℝ)*α-(p:ℝ)|) := by
    by_cases h : 0<i.val
    · obtain ⟨ε,hε,hbound⟩ := multiple_separation α hi i.val h
      exact ⟨ε,hε,fun _ => hbound⟩
    · exact ⟨1,by norm_num,fun hh => False.elim (h hh)⟩
  choose ε hε using hex
  obtain ⟨i,_hi,hmin⟩ := Finset.exists_min_image Finset.univ ε (by simp)
  obtain ⟨K,hK⟩ := exists_nat_gt (1/ε i)
  have hKR : (0:ℝ)<K := lt_trans (one_div_pos.mpr (hε i).1) hK
  have hKn : 0<K := by exact_mod_cast hKR
  have hinv : 1/(K:ℝ)<ε i := by
    apply (div_lt_iff hKR).mpr
    have hh := (div_lt_iff (hε i).1).mp hK
    nlinarith
  obtain ⟨p,q,hq,hqK,herr,_⟩ := bounded_denominator α K hKn
  have hqB : B<q := by
    by_contra h
    let j : Fin (B+1) := ⟨q,by omega⟩
    have hlow := (hε j).2 hq p
    have hmin' := hmin j (by simp)
    change ε j≤|(q:ℝ)*α-(p:ℝ)| at hlow
    linarith
  refine ⟨p,q,hqB,lt_of_lt_of_le herr ?_⟩
  exact one_div_le_one_div_of_le (by exact_mod_cast hq) (by exact_mod_cast hqK)

theorem rational_approximations_unbounded (α : ℝ) (hi : Irrational α) (B : ℕ) :
    ∃ p : ℤ, ∃ q : ℕ, B<q ∧ |(p:ℝ)/(q:ℝ)-α| ≤ 1/(q:ℝ)^2 := by
  /-
  Theorem: For an irrational input, fractions satisfying the quadratic
  error bound have arbitrarily large denominators. Proof: Use the
  unbounded-denominator multiple approximation, reverse the difference
  inside its absolute value, and apply the scaling equivalence. QED
  -/
  obtain ⟨p,q,hq,he⟩ := unbounded_denominators α hi B
  refine ⟨p,q,hq,(scaled_approximation_iff α p q (by omega)).mpr ?_⟩
  rw [abs_sub_comm]
  exact he.le

theorem avoid_finite_approximations (α : ℝ) (hi : Irrational α) (xs : List ℚ) :
    ∃ p : ℤ, ∃ q : ℕ, 0<q ∧ (p:ℚ)/(q:ℚ) ∉ xs ∧
      |(p:ℝ)/(q:ℝ)-α| ≤ 1/(q:ℝ)^2 := by
  /-
  Theorem: Infinitely many distinct rational values satisfy the quadratic
  approximation bound. Proof: Start with any finite list of fractions.
  Irrationality makes every distance from alpha to a listed value
  positive, so the finite list has a positive common lower bound on
  those distances. Take an approximation with denominator so large
  that 1/q^2 is smaller than this bound. It cannot be in the list.
  The empty list has lower bound one. QED
  -/
  have separation : ∃ ε : ℝ, 0<ε ∧ ∀ r ∈ xs, ε≤|(r:ℝ)-α| := by
    induction xs with
    | nil => exact ⟨1,by norm_num,by simp⟩
    | cons r rs ih =>
      obtain ⟨ε,hε,hrs⟩ := ih
      have hr : (r:ℝ)≠α := by
        intro hh
        apply hi r.num r.den r.pos
        rw [← hh]
        exact Rat.cast_def r
      have hd : 0 < |(r:ℝ)-α| := abs_pos.mpr (sub_ne_zero.mpr hr)
      refine ⟨min ε |(r:ℝ)-α|,lt_min hε hd,?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with hs|hs
      · subst s; exact min_le_right _ _
      · exact le_trans (min_le_left _ _) (hrs s hs)
  obtain ⟨ε,hε,hsep⟩ := separation
  obtain ⟨B,hB⟩ := exists_nat_gt (1/ε)
  obtain ⟨p,q,hq,he⟩ := rational_approximations_unbounded α hi B
  have hq0 : 0<q := by omega
  have hqR : (0:ℝ)<q := by exact_mod_cast hq0
  have hBq : (B:ℝ)<q := by exact_mod_cast hq
  have hsmall : 1/(q:ℝ)<ε := by
    apply (div_lt_iff hqR).mpr
    have hh := (div_lt_iff hε).mp (lt_trans hB hBq)
    nlinarith
  have hsq : (q:ℝ)≤(q:ℝ)^2 := by
    have h1 : (1:ℝ)≤q := by exact_mod_cast hq0
    nlinarith
  have herr : |(p:ℝ)/(q:ℝ)-α|<ε := lt_of_le_of_lt
    (le_trans he (one_div_le_one_div_of_le hqR hsq)) hsmall
  refine ⟨p,q,hq0,?_,he⟩
  intro hmem
  have hh := hsep ((p:ℚ)/(q:ℚ)) hmem
  push_cast at hh
  linarith

theorem nonsquare_root_irrational (N : ℕ) (hN : 0<N)
    (hns : ∀ k : ℕ, N≠k*k) : Irrational (Real.sqrt (N:ℝ)) := by
  /-
  Lemma: The positive square root of a nonsquare integer is irrational.
  Proof: Suppose sqrt(N)=a/b with b>0. Squaring and clearing the
  denominator gives a*a=N*b*b. The earlier square-divisibility result
  implies b divides |a|, say |a|=b*k. Substitution and cancellation
  of b*b give N=k*k, contrary to the nonsquare hypothesis. QED
  -/
  intro a b hb he
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hNreal : (0:ℝ)<N := by exact_mod_cast hN
  have hs := Real.sqrt_pos.mpr hNreal
  have hm : (a:ℝ)=Real.sqrt (N:ℝ)*(b:ℝ) := ((eq_div_iff (ne_of_gt hbR)).mp he).symm
  have haR : (0:ℝ)<a := by rw [hm]; exact mul_pos hs hbR
  have ha : (0:ℤ)<a := by exact_mod_cast haR
  have haabs : 0<a.natAbs := Int.natAbs_pos.mpr (ne_of_gt ha)
  have heR : (a:ℝ)^2=(N:ℝ)*(b:ℝ)^2 := by
    rw [hm,mul_pow,Real.sq_sqrt hNreal.le]
  have heI : a^2=(N:ℤ)*(b:ℤ)^2 := by exact_mod_cast heR
  have heA : a.natAbs^2=N*b^2 := by
    have hh := congrArg Int.natAbs heI
    simpa only [Int.natAbs_pow,Int.natAbs_mul,Int.natAbs_ofNat] using hh
  have hd : b^2 ∣ a.natAbs^2 := ⟨N,by rw [heA]; ac_rfl⟩
  obtain ⟨k,hk⟩ := NumberTheory.DivisibilityTests.dvd_of_square_dvd b a.natAbs hb haabs hd
  apply hns k
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hb : 0<b^2)
  rw [hk,mul_pow] at heA
  nlinarith [heA]

end NumberTheory.RationalApproximations
