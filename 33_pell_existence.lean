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

theorem fixed_norm_unbounded (N : ℕ) (hN : 0<N) (hns : ∀ k : ℕ, N≠k*k) :
    ∃ K : ℤ, K≠0 ∧ ∀ B : ℕ, ∃ x y : ℕ,
      0<x ∧ B<y ∧ (x:ℤ)^2-(N:ℤ)*(y:ℤ)^2=K := by
  /-
  Theorem: For a positive nonsquare N, one nonzero integer K occurs as
  x*x-N*y*y for positive x and arbitrarily large positive y.
  Proof: For each index i choose an approximation with denominator y>i.
  Since sqrt(N)>=1 and its error is less than 1/y<=1, its numerator
  is positive. The preceding norm bound puts every integer value in
  the same finite interval. Label each value by its position in that
  interval. The recurrence lemma gives one value at arbitrarily late
  indices, and hence at arbitrarily large denominators. A zero value
  would make sqrt(N)=x/y, contradicting its previously proved
  irrationality. Unbounded denominators imply infinitely many distinct
  positive pairs. The standing nonsquare hypothesis is explicit. QED
  -/
  classical
  have hI := nonsquare_root_irrational N hN hns
  choose p q hq he using fun i => unbounded_denominators (Real.sqrt (N:ℝ)) hI i
  have hq0 (i) : 0<q i := by have := hq i; omega
  have hs0 := Real.sqrt_nonneg (N:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤N by positivity)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hs1 : 1≤Real.sqrt (N:ℝ) := by nlinarith only [hs0,hs2,hN1]
  have hp (i) : 0<p i := by
    have hq1 : (1:ℝ)≤q i := by exact_mod_cast hq0 i
    have hi : 1/(q i:ℝ)≤1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1
    have hh := (abs_lt.mp (he i)).2
    have hmul : (1:ℝ)≤(q i:ℝ)*Real.sqrt N := by nlinarith only [hq1,hs1]
    have : (0:ℝ)<p i := by linarith only [hh,hi,hmul]
    exact_mod_cast this
  let x (i : ℕ) := (p i).natAbs
  have hx (i) : (x i:ℤ)=p i := Int.natAbs_of_nonneg (hp i).le
  have hxR (i) : (x i:ℝ)=(p i:ℝ) := by exact_mod_cast hx i
  let v (i : ℕ) : ℤ := (p i)^2-(N:ℤ)*(q i:ℤ)^2
  obtain ⟨M,hM⟩ := exists_nat_gt (3*Real.sqrt (N:ℝ))
  have hb (i) : -(M:ℤ)<v i ∧ v i<(M:ℤ) := by
    have hh := approximation_norm_bound N (x i) (q i) hN
      (Int.natAbs_pos.mpr (ne_of_gt (hp i))) (hq0 i)
      (by rw [hxR i,abs_sub_comm]; exact he i)
    rw [hxR i] at hh
    have hh' : |((v i:ℤ):ℝ)|<(M:ℝ) := by
      dsimp [v]; push_cast; exact lt_trans hh hM
    have hh'' := abs_lt.mp hh'
    exact_mod_cast hh''
  let label (i : ℕ) := (v i+(M:ℤ)).toNat
  have hl (i) : label i<2*M+1 := by
    have := hb i
    have hc : ((v i+(M:ℤ)).toNat:ℤ)=v i+(M:ℤ) := Int.toNat_of_nonneg (by omega)
    dsimp [label]
    omega
  obtain ⟨k,_,hk⟩ := recurring_label (List.range (2*M+1)) label
    (fun i => List.mem_range.mpr (hl i))
  have hv (i) (hi : label i=k) : v i=(k:ℤ)-(M:ℤ) := by
    have := hb i
    have hc : ((v i+(M:ℤ)).toNat:ℤ)=v i+(M:ℤ) := Int.toNat_of_nonneg (by omega)
    dsimp [label] at hi
    omega
  refine ⟨(k:ℤ)-(M:ℤ),?_,?_⟩
  · obtain ⟨i,_,hi⟩ := hk 0
    intro hz
    have hv0 : v i=0 := (hv i hi).trans hz
    have hvR : (p i:ℝ)^2=(N:ℝ)*(q i:ℝ)^2 := by
      have hh : (p i)^2=(N:ℤ)*(q i:ℤ)^2 := by dsimp [v] at hv0; omega
      exact_mod_cast hh
    have hpR : (0:ℝ)<p i := by exact_mod_cast hp i
    have hqR : (0:ℝ)<q i := by exact_mod_cast hq0 i
    apply hI (p i) (q i) (hq0 i)
    apply (eq_div_iff (ne_of_gt hqR)).mpr
    have hh : (Real.sqrt (N:ℝ)*(q i:ℝ))^2=(p i:ℝ)^2 := by
      rw [mul_pow,hs2]
      exact hvR.symm
    exact (sq_eq_sq (mul_nonneg hs0 hqR.le) hpR.le).mp hh
  · intro B
    obtain ⟨i,hi,hki⟩ := hk B
    refine ⟨x i,q i,Int.natAbs_pos.mpr (ne_of_gt (hp i)),by have := hq i; omega,?_⟩
    rw [hx i]
    exact hv i hki

theorem repeated_residue_pair (n : ℕ) (hn : 0<n) (x y : ℕ → ℤ) :
    ∃ i j : ℕ, i≠j ∧ (n:ℤ)∣x i-x j ∧ (n:ℤ)∣y i-y j := by
  /-
  Lemma: In any infinite sequence of integer pairs, two distinct
  positions have both coordinates congruent modulo a positive n.
  Proof: Each coordinate has one of n remainders, so a pair has one
  of n*n remainder labels. Among the first n*n+1 positions two have
  the same label, by finite pigeonhole counting. Equal remainders
  say exactly that n divides each coordinate difference. The pairs
  need not themselves be different; the indices are different. The
  modulus is explicitly positive, since the assertion fails at zero.
  QED
  -/
  have hnI : (0:ℤ)<n := by exact_mod_cast hn
  let rem (z : ℤ) : Fin n := ⟨(z%(n:ℤ)).toNat,by
    have h0 := Int.emod_nonneg z (ne_of_gt hnI)
    have h1 := Int.emod_lt_of_pos z hnI
    have hc := Int.toNat_of_nonneg h0
    omega⟩
  let f (i : Fin (n*n+1)) := (rem (x i),rem (y i))
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hx : x i%(n:ℤ)=x j%(n:ℤ) := by
    have hh := congrArg (fun z : Fin n × Fin n => z.1.val) he
    dsimp [f,rem] at hh
    have hi := Int.emod_nonneg (x i) (ne_of_gt hnI)
    have hj := Int.emod_nonneg (x j) (ne_of_gt hnI)
    have hi' := Int.toNat_of_nonneg hi
    have hj' := Int.toNat_of_nonneg hj
    omega
  have hy : y i%(n:ℤ)=y j%(n:ℤ) := by
    have hh := congrArg (fun z : Fin n × Fin n => z.2.val) he
    dsimp [f,rem] at hh
    have hi := Int.emod_nonneg (y i) (ne_of_gt hnI)
    have hj := Int.emod_nonneg (y j) (ne_of_gt hnI)
    have hi' := Int.toNat_of_nonneg hi
    have hj' := Int.toNat_of_nonneg hj
    omega
  exact ⟨i,j,(fun h => hne (Fin.ext h)),
    Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hx),
    Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hy)⟩

end NumberTheory.PellExistence
