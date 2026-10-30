import «28_hypotenuses»

namespace NumberTheory.FourthPowers

open NumberTheory.CommonDivisors
open NumberTheory.DivisibilityTests
open NumberTheory.RightTriangles
open NumberTheory.Hypotenuses (coprime_prime_test)
open NumberTheory.Factorization (Prime)

theorem coprime_legs_primitive (a b c : Int) (h : Triple a b c)
    (hc : gcd a b=1) : Primitive a b c := by
  /-
  Lemma: A positive integer right triangle with coprime legs is primitive.
  Proof: A common divisor of its sides divides both legs and hence their
  Bezout combination one. A positive divisor of one is one. QED
  -/
  refine ⟨h,?_⟩
  intro d hd ha hb _
  obtain ⟨u,v,he⟩ := coprime_bezout a b hc
  have hh := dvd_linear d a b u v ha hb
  rw [he] at hh
  have := divisor_le_positive d 1 (by decide) hh
  omega

theorem primitive_fourth_descent (x y z : Int) (hx : 0<x) (hy : 0<y)
    (h : Primitive (x*x) (y*y) z) (heven : (x*x)%2=0) :
    ∃ d e f : Int, 0<d ∧ 0<e ∧ 0<f ∧ f<z ∧
      (d*d)*(d*d)+(e*e)*(e*e)=f*f := by
  /-
  Lemma: A primitive right triangle whose legs are squares produces a
  smaller solution of the fourth-power equation.
  Proof: Put the even leg first.
  Its parameters give x*x=2*s*t, y*y=s*s-t*t, z=s*s+t*t.
  The larger parameter s is odd: otherwise the odd square y*y would
  have remainder three modulo four. Thus s and 2*t are coprime, and
  their square product makes s=f*f and 2*t=k*k. The new triangle
  (t,y,s) is primitive, with t even. Its parameters give t=2*u*v and
  s=u*u+v*v, with u,v coprime. Since k is even, (k/2)^2=u*v;
  hence u=d*d and v=e*e. Consequently d^4+e^4=f*f. All roots are
  positive, and f<=f*f=s<z, which is the required decrease. QED
  -/
  obtain ⟨s,t,ht,hst,hcop,hpar,hx2,hy2,hz⟩ :=
    primitive_parameters (x*x) (y*y) z h heven
  have hs : 0<s := by omega
  have hsodd : s%2=1 := by
    have hsq := square_residue_four y
    have hh := congrArg (fun n : Int => n%4) hy2
    dsimp only at hh
    rw [Int.sub_emod,Int.mul_emod s s 4,Int.mul_emod t t 4] at hh
    have sr : s%4=0 ∨ s%4=1 ∨ s%4=2 ∨ s%4=3 := by omega
    have tr : t%4=0 ∨ t%4=1 ∨ t%4=2 ∨ t%4=3 := by omega
    rcases sr with sr|sr|sr|sr <;> rcases tr with tr|tr|tr|tr <;>
      rw [sr,tr] at hh <;> omega
  have hteven : t%2=0 := by omega
  have hs2 : gcd s 2=1 := by
    apply coprime_of_bezout s 2 1 (-(s/2))
    omega
  have hsc := coprime_right_product s 2 t hs2 hcop
  obtain ⟨f,k,hf,hk,hsf,htk⟩ := coprime_square_factors s (2*t) x hs (by omega) hx hsc
    (by rw [hx2]; simp only [Int.mul_assoc,Int.mul_comm,Int.mul_left_comm])
  have hty : gcd t y=1 := by
    apply (coprime_prime_test t y).mpr
    intro p hp hdiv
    have hds : (p:Int) ∣ s*s := by
      have hsum : s*s=t*t+y*y := by omega
      rw [hsum]
      exact dvd_linear p t y t y hdiv.1 hdiv.2
    have hd := (prime_dvd_integer_product p hp s s hds).elim id id
    exact (coprime_prime_test s t).mp hcop p hp ⟨hd,hdiv.1⟩
  have htri : Primitive t y s := coprime_legs_primitive t y s
    ⟨ht,hy,hs,by omega⟩ hty
  obtain ⟨u,v,hv,hvu,huv,_hpar,htuv,_hyuv,hsuv⟩ :=
    primitive_parameters t y s htri hteven
  have hu : 0<u := by omega
  have hkeven : k%2=0 := by
    have hh := congrArg (fun n : Int => n%4) htk
    dsimp only at hh
    rw [Int.mul_emod 2 t 4,Int.mul_emod k k 4] at hh
    have tr : t%4=0 ∨ t%4=2 := by omega
    have kr : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3 := by omega
    rcases tr with tr|tr <;> rcases kr with kr|kr|kr|kr <;>
      rw [tr,kr] at hh <;> omega
  let w := k/2
  have hkw : k=2*w := by dsimp [w]; omega
  have hw : 0<w := by omega
  have huvww : u*v=w*w := by
    rw [htuv,hkw] at htk
    have hleft : 2*(2*u*v)=4*(u*v) := by simp only [← Int.mul_assoc]; rfl
    have hright : (2*w)*(2*w)=4*(w*w) := by
      calc
        (2*w)*(2*w) = (2*2)*(w*w) := by ac_rfl
        _ = 4*(w*w) := rfl
    rw [hleft,hright] at htk
    omega
  obtain ⟨d,e,hd,he,hud,hve⟩ := coprime_square_factors u v w hu hv hw huv huvww
  have hfbound : f≤s := by
    have hh := Int.mul_le_mul_of_nonneg_left (show 1≤f by omega) (show 0≤f by omega)
    simp only [Int.mul_one] at hh
    omega
  have hsbound : s<z := by
    have hh := Int.mul_le_mul_of_nonneg_left (show 1≤s by omega) (show 0≤s by omega)
    simp only [Int.mul_one] at hh
    have := Int.mul_pos ht ht
    omega
  refine ⟨d,e,f,hd,he,hf,by omega,?_⟩
  rw [← hud,← hve,← hsuv,← hsf]

end NumberTheory.FourthPowers
