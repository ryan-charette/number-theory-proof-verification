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

theorem signed_values {N : ℕ} {r s : ℤ} (h : PellSolution N r s) :
    Represents N (value N r (-s)) ∧ Represents N (value N (-r) s) ∧
    Represents N (value N (-r) (-s)) := by
  /-
  Each of the three expressions uses the original pair with one or
  both signs changed. The equation involves each coordinate only
  through its square. Consequently each indicated pair is itself
  a witness that the corresponding real value represents a solution. QED
  -/
  refine ⟨⟨r,-s,(inverse_solution h).2,rfl⟩,⟨-r,s,?_,rfl⟩,⟨-r,-s,?_,rfl⟩⟩ <;>
    simpa [PellSolution] using h

def PositiveSolution (N : ℕ) (z : ℝ) : Prop :=
  ∃ r s : ℕ, 0<r ∧ 0<s ∧ PellSolution N (r:ℤ) (s:ℤ) ∧ z=value N r s

theorem positive_iff {N : ℕ} (hN : 0<N) (z : ℝ) :
    PositiveSolution N z ↔ Represents N z ∧ 1<z := by
  /-
  With positive coordinates, r is at least one and s√N is positive,
  so their sum exceeds one. Conversely suppose z=r+s√N exceeds one.
  Its reciprocal r-s√N is positive and less than one. Adding these
  values gives 2r>0. Subtracting gives 2s√N>0, so s>0 as well.
  The two positive integers therefore give positive natural coordinates. QED
  -/
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  constructor
  · rintro ⟨r,s,hr,ht,h, rfl⟩
    refine ⟨⟨r,s,h,rfl⟩,?_⟩
    have hr1 : (1:ℝ)≤r := by exact_mod_cast hr
    have ht0 : (0:ℝ)<s := by exact_mod_cast ht
    unfold value
    push_cast
    linarith only [hr1,mul_pos ht0 hs]
  · rintro ⟨⟨r,s,h,rfl⟩,hz⟩
    have hi := (inverse_solution h).1
    have hp : 0<value N r (-s) := hi ▸ inv_pos.mpr (by linarith : 0<value N r s)
    have hl : value N r (-s)<1 := by
      rw [← hi,inv_eq_one_div]
      apply (div_lt_iff (by linarith : 0<value N r s)).mpr
      simpa using hz
    simp only [value,Int.cast_neg] at hp hl hz
    have hrR : (0:ℝ)<r := by linarith
    have hsR : (0:ℝ)<s := by by_contra! hn; nlinarith only [hl,hz,mul_nonpos_of_nonpos_of_nonneg hn hs.le]
    have hr : 0<r := by exact_mod_cast hrR
    have ht : 0<s := by exact_mod_cast hsR
    have hrc := Int.toNat_of_nonneg hr.le
    have hsc := Int.toNat_of_nonneg ht.le
    refine ⟨r.toNat,s.toNat,by omega,by omega,?_,?_⟩ <;>
      simp only [Int.toNat_of_nonneg hr.le,Int.toNat_of_nonneg ht.le]
    exact h

theorem least_positive_solution (N : ℕ) (hN : 0<N) (hns : ∀ k : ℕ, N≠k*k) :
    ∃ ε : ℝ, PositiveSolution N ε ∧ ∀ z, PositiveSolution N z → ε≤z := by
  /-
  There is at least one positive pair by the existence theorem. Among
  its possible first coordinates choose the least, r, by well-ordering,
  and let s be a corresponding second coordinate. For any other pair
  (a,b), r≤a gives r²≤a². Subtract one on both sides to obtain
  Ns²≤Nb². Since N is positive and both coordinates are nonnegative,
  s≤b. Adding the coordinate inequalities after multiplying the second
  by √N shows that r+s√N is the least positive solution value. QED
  -/
  classical
  let P (r : ℕ) := ∃ s : ℕ, 0<r ∧ 0<s ∧ PellSolution N (r:ℤ) (s:ℤ)
  have hex : ∃ r, P r := positive_solution_exists N hN hns
  let r := Nat.find hex
  obtain ⟨s,hr,hs,hpair⟩ := Nat.find_spec hex
  refine ⟨value N r s,⟨r,s,hr,hs,hpair,rfl⟩,?_⟩
  rintro z ⟨a,b,ha,hb,hab,rfl⟩
  have hra : r≤a := Nat.find_min' hex (show P a from ⟨b,ha,hb,hab⟩)
  have hraI : (r:ℤ)≤a := by exact_mod_cast hra
  have hsq := mul_self_le_mul_self (show (0:ℤ)≤r by positivity) hraI
  change (r:ℤ)*r-(N:ℤ)*((s:ℤ)*s)=1 at hpair
  change (a:ℤ)*a-(N:ℤ)*((b:ℤ)*b)=1 at hab
  have hsb : s≤b := by
    by_contra! h
    have hbs : (b:ℤ)<s := by exact_mod_cast h
    have hlt := mul_self_lt_mul_self (show (0:ℤ)≤b by positivity) hbs
    have hN' : (0:ℤ)<N := by exact_mod_cast hN
    linarith only [hsq,hpair,hab,mul_lt_mul_of_pos_left hlt hN']
  unfold value
  push_cast
  exact add_le_add (by exact_mod_cast hra)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hsb) (Real.sqrt_nonneg _))

end NumberTheory.PellPowers
