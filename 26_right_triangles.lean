import «05_divisibility_tests»

namespace NumberTheory.RightTriangles

open NumberTheory.CommonDivisors
open NumberTheory.DivisibilityTests (coprime_divisors coprime_right_product)

/-
A triple consists of positive integers satisfying the right-triangle equation.
Primitive means that its three entries have no positive common divisor but one.
All parameters called positive below are explicitly required to exceed zero.
-/
theorem square_residue_four (a : Int) : a*a % 4 = 0 ∨ a*a % 4 = 1 := by
  /-
  Lemma: A square leaves remainder zero or one on division by four.
  Proof: The base has remainder zero, one, two, or three. Squaring
  these four possibilities gives remainders zero, one, zero, one. QED
  -/
  have h : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases h with h | h | h | h <;> rw [Int.mul_emod, h] <;> decide

def Triple (a b c : Int) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ a*a + b*b = c*c

theorem even_leg (a b c : Int) (h : Triple a b c) : a % 2 = 0 ∨ b % 2 = 0 := by
  /-
  Theorem: At least one leg of a right triangle with integer sides is even.
  Proof: If both legs were odd, each square would leave remainder one
  modulo four. Their sum would leave remainder two, whereas the square
  of the hypotenuse leaves remainder zero or one. QED
  -/
  have hc := square_residue_four c
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have hb : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  have he := congrArg (fun x : Int => x % 4) h.2.2.2
  change (a*a+b*b)%4=(c*c)%4 at he
  rw [Int.add_emod, Int.mul_emod a, Int.mul_emod b] at he
  rcases ha with ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb <;> simp only [ha, hb] at he <;> omega

theorem scale_triple (a b c d : Int) (h : Triple a b c) (hd : 0 < d) :
    Triple (d*a) (d*b) (d*c) := by
  /-
  Theorem: Multiplying every side by a positive integer gives another triple.
  Proof: The new sides are positive. Multiply the original equation by
  d*d and distribute; its terms are precisely the three new squares. QED
  -/
  refine ⟨Int.mul_pos hd h.1, Int.mul_pos hd h.2.1, Int.mul_pos hd h.2.2.1, ?_⟩
  have he := congrArg (fun x => d*d*x) h.2.2.2
  simpa only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using he

theorem parameter_triple (s t : Int) (ht : 0 < t) (hst : t < s) :
    Triple (2*s*t) (s*s-t*t) (s*s+t*t) := by
  /-
  Theorem: Positive integers s>t give the triple
  (2*s*t, s*s-t*t, s*s+t*t).
  Proof: Both products are positive, and s*s>t*t follows by multiplying
  the strict inequality between the positive parameters. Expanding gives
  (s*s-t*t)^2+4*s*s*t*t=(s*s+t*t)^2. QED
  -/
  have hs : 0 < s := by omega
  have hsq : t*t < s*s := by
    have := Int.mul_lt_mul_of_pos_left hst ht
    have := Int.mul_lt_mul_of_pos_right hst hs
    omega
  refine ⟨Int.mul_pos (Int.mul_pos (by decide) hs) ht, by omega,
    by have := Int.mul_pos hs hs; have := Int.mul_pos ht ht; omega, ?_⟩
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  simp only [← Int.mul_assoc]
  omega

def Primitive (a b c : Int) : Prop :=
  Triple a b c ∧ ∀ d : Int, 0 < d → d ∣ a → d ∣ b → d ∣ c → d = 1

theorem primitive_parity (a b c : Int) (h : Primitive a b c) :
    ((a % 2 = 0 ∧ b % 2 = 1) ∨ (a % 2 = 1 ∧ b % 2 = 0)) ∧ c % 2 = 1 := by
  /-
  Theorem: In a primitive triple exactly one leg is even, and the hypotenuse
  is odd. Proof: There is an even leg. Modulo two a square has the same
  remainder as its base. Thus if both legs were even, so would be the
  hypotenuse, contradicting primitivity with common divisor two.
  The remaining two parity possibilities both give an odd hypotenuse. QED
  -/
  have he := h.1.2.2.2
  have hm : (a*a+b*b)%2=(c*c)%2 := congrArg (fun x : Int => x%2) he
  rw [Int.add_emod, Int.mul_emod a, Int.mul_emod b, Int.mul_emod c] at hm
  have ha : a%2=0 ∨ a%2=1 := by omega
  have hb : b%2=0 ∨ b%2=1 := by omega
  have hc : c%2=0 ∨ c%2=1 := by omega
  have hn : ¬ (a%2=0 ∧ b%2=0 ∧ c%2=0) := by
    intro ht
    have := h.2 2 (by decide) (Int.dvd_of_emod_eq_zero ht.1)
      (Int.dvd_of_emod_eq_zero ht.2.1) (Int.dvd_of_emod_eq_zero ht.2.2)
    omega
  have hl := even_leg a b c h.1
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> simp only [ha, hb, hc] at hm <;> omega

theorem primitive_leg_hypotenuse_coprime (a b c : Int) (h : Primitive a b c) :
    gcd b c = 1 := by
  /-
  Lemma: The second leg and hypotenuse of a primitive triple are coprime.
  Proof: Let d be their positive gcd. Since d divides b and c, its square
  divides c*c-b*b=a*a. The earlier square-divisibility result implies d
  divides a as well. Primitivity now gives d=1. QED
  -/
  let d := gcd b c
  have hd : 0 < d := gcd_positive b c (Or.inl (by have := h.1.2.1; omega))
  have hb : d ∣ b := (gcd_data b c).2.1
  have hc : d ∣ c := (gcd_data b c).2.2.1
  have hs : d*d ∣ a*a := by
    rcases hb with ⟨u, hu⟩
    rcases hc with ⟨v, hv⟩
    refine ⟨v*v-u*u, ?_⟩
    have he := h.1.2.2.2
    rw [hu, hv] at he
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at he ⊢
    omega
  have hn : d.natAbs^2 ∣ a.natAbs^2 := by
    have hn := Int.natAbs_dvd_natAbs.mpr hs
    simpa only [Int.natAbs_mul, Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul] using hn
  have ha : d ∣ a := Int.natAbs_dvd_natAbs.mp
    (NumberTheory.DivisibilityTests.dvd_of_square_dvd _ _
      (Int.natAbs_pos.mpr (by omega))
      (Int.natAbs_pos.mpr (by have := h.1.1; omega)) hn)
  exact h.2 d hd ha hb hc

theorem coprime_square_factors (x y z : Int) (hx : 0 < x) (_hy : 0 < y)
    (hz : 0 < z) (hc : gcd x y = 1) (he : x*y=z*z) :
    ∃ s t : Int, 0 < s ∧ 0 < t ∧ x=s*s ∧ y=t*t := by
  /-
  Lemma: Positive coprime factors of a square are themselves squares.
  Proof: Remove d=gcd(x,z), writing x=d*X and z=d*Z with X,Z coprime.
  Cancellation gives X*y=d*Z*Z. Since X is coprime to Z*Z, X divides d;
  write d=X*k. Cancelling X gives y=k*Z*Z, and x=k*X*X. All the
  quotients are positive. Thus k is a positive common divisor of x,y,
  so k=1. The positive square roots are X and Z. QED
  -/
  let d := gcd x z
  let X := x/d
  let Z := z/d
  have hd : 0 < d := gcd_positive x z (Or.inl (by omega))
  have hq := gcd_quotients x z
  change x=d*X ∧ z=d*Z at hq
  have hX : 0 < X := by
    by_cases hh : 0 < X
    · exact hh
    · have := Int.mul_le_mul_of_nonneg_left (show X ≤ 0 by omega) (show 0 ≤ d by omega)
      simp only [Int.mul_zero] at this
      omega
  have hZ : 0 < Z := by
    by_cases hh : 0 < Z
    · exact hh
    · have := Int.mul_le_mul_of_nonneg_left (show Z ≤ 0 by omega) (show 0 ≤ d by omega)
      simp only [Int.mul_zero] at this
      omega
  have hcop : gcd X Z = 1 := reduced_coprime x z (Or.inl (by omega))
  have hr : X*y=d*(Z*Z) := by
    apply Int.eq_of_mul_eq_mul_left (a := d) (by omega)
    calc
      d*(X*y) = x*y := by rw [← Int.mul_assoc, ← hq.1]
      _ = z*z := he
      _ = d*(d*(Z*Z)) := by rw [hq.2]; simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hdiv : X ∣ (Z*Z)*d := ⟨y, by rw [Int.mul_comm (Z*Z) d]; exact hr.symm⟩
  rcases coprime_dvd_cancel X (Z*Z) d hdiv (coprime_right_product X Z Z hcop hcop) with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_cases hh : 0 < k
    · exact hh
    · have := Int.mul_le_mul_of_nonneg_left (show k ≤ 0 by omega) (show 0 ≤ X by omega)
      simp only [Int.mul_zero] at this
      omega
  have hyy : y=k*(Z*Z) := by
    apply Int.eq_of_mul_eq_mul_left (a := X) (by omega)
    rw [hr, hk, Int.mul_assoc]
  have hxx : x=k*(X*X) := by
    rw [hq.1, hk]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hkone : k=1 := by
    rcases coprime_bezout x y hc with ⟨u,v,huv⟩
    have hdvd : k ∣ 1 := by
      rw [← huv]
      exact dvd_linear k x y u v ⟨X*X,hxx⟩ ⟨Z*Z,hyy⟩
    have := divisor_le_positive k 1 (by decide) hdvd
    omega
  exact ⟨X,Z,hX,hZ,by simpa [hkone] using hxx,by simpa [hkone] using hyy⟩

theorem primitive_half_squares (a b c : Int) (h : Primitive a b c) (ha : a%2=0) :
    ∃ s t : Int, 0 < t ∧ t < s ∧ gcd s t=1 ∧ c+b=2*(s*s) ∧ c-b=2*(t*t) := by
  /-
  Lemma: For a primitive triple with even first leg, the half-sum and
  half-difference of the hypotenuse and odd leg are coprime squares.
  Proof: Put u=(c+b)/2, v=(c-b)/2, w=a/2. The hypotenuse exceeds b
  because a is positive, so u>v>0. Parity makes these integer halves
  exact. Their product is w*w. A common divisor of u,v divides
  u-v=b and u+v=c, so they are coprime. Apply the coprime-square-factor
  lemma to obtain u=s*s and v=t*t with positive roots. These roots
  are coprime as divisors of u,v, and u>v gives s>t. QED
  -/
  have hp := primitive_parity a b c h
  have hb : b%2=1 := by omega
  have hcb : b<c := by
    by_cases hh : b<c
    · exact hh
    · have hs := Int.mul_self_le_mul_self (show 0 ≤ c by have := h.1.2.2.1; omega)
        (show c ≤ b by omega)
      have := Int.mul_pos h.1.1 h.1.1
      have := h.1.2.2.2
      omega
  let u := (c+b)/2
  let v := (c-b)/2
  let w := a/2
  have hu : 2*u=c+b := by dsimp [u]; omega
  have hv : 2*v=c-b := by dsimp [v]; omega
  have hw : 2*w=a := by dsimp [w]; omega
  have hup : 0 < u := by have := h.1.2.1; omega
  have hvp : 0 < v := by omega
  have hwp : 0 < w := by have := h.1.1; omega
  have huv : v<u := by have := h.1.2.1; omega
  have hsum : u+v=c := by omega
  have hdiff : u-v=b := by omega
  have hcop : gcd u v=1 := by
    rcases coprime_bezout b c (primitive_leg_hypotenuse_coprime a b c h) with ⟨i,j,hij⟩
    apply coprime_of_bezout u v (i+j) (j-i)
    rw [← hsum, ← hdiff] at hij
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
      Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] at hij ⊢
    omega
  have he : u*v=w*w := by
    have he := h.1.2.2.2
    rw [← hw, ← hdiff, ← hsum] at he
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
      Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] at he
    simp only [← Int.mul_assoc] at he
    rw [show (2:Int)*2=4 from rfl] at he
    rw [Int.mul_assoc 4 w w] at he
    omega
  rcases coprime_square_factors u v w hup hvp hwp hcop he with ⟨s,t,hs,ht,hus,hvt⟩
  have hst : t<s := by
    by_cases hh : t<s
    · exact hh
    · have := Int.mul_self_le_mul_self (show 0 ≤ s by omega) (show s ≤ t by omega)
      omega
  have hroots : gcd s t=1 := coprime_divisors u v s t hcop ⟨s,hus⟩ ⟨t,hvt⟩
  exact ⟨s,t,ht,hst,hroots,by omega,by omega⟩

theorem primitive_parameters (a b c : Int) (h : Primitive a b c) (ha : a%2=0) :
    ∃ s t : Int, 0 < t ∧ t < s ∧ gcd s t=1 ∧ s%2≠t%2 ∧
      a=2*s*t ∧ b=s*s-t*t ∧ c=s*s+t*t := by
  /-
  Theorem: Every primitive triple with even first leg comes from positive
  coprime parameters s>t of opposite parity.
  Proof: The half-squares lemma gives c+b=2*s*s and c-b=2*t*t.
  Addition and subtraction give c=s*s+t*t and b=s*s-t*t. Substitution
  into the triple equation shows a*a=(2*s*t)^2. Both bases are positive,
  so they are equal. Since b is odd, its expression as a difference
  of squares forces s,t to have opposite parity. QED
  -/
  rcases primitive_half_squares a b c h ha with ⟨s,t,ht,hst,hcop,hsq,htq⟩
  have hb : b=s*s-t*t := by omega
  have hc : c=s*s+t*t := by omega
  have hg := parameter_triple s t ht hst
  have hae : a*a=(2*s*t)*(2*s*t) := by
    have he := h.1.2.2.2
    rw [hb,hc] at he
    have hf := hg.2.2.2
    omega
  have haa : a=2*s*t := by
    by_cases hh : a<2*s*t
    · have := Int.mul_self_lt_mul_self (show 0 ≤ a by have := h.1.1; omega) hh
      omega
    · by_cases hh' : 2*s*t<a
      · have := Int.mul_self_lt_mul_self (show 0 ≤ 2*s*t by have := hg.1; omega) hh'
        omega
      · omega
  have hodd : b%2=1 := by have := primitive_parity a b c h; omega
  have hpar : s%2≠t%2 := by
    intro he
    have hm : b%2=(s*s-t*t)%2 := congrArg (fun x : Int => x%2) hb
    rw [Int.sub_emod, Int.mul_emod s, Int.mul_emod t, he] at hm
    have hh : t%2=0 ∨ t%2=1 := by omega
    rcases hh with hh | hh <;> rw [hh] at hm <;> omega
  exact ⟨s,t,ht,hst,hcop,hpar,haa,hb,hc⟩

end NumberTheory.RightTriangles
