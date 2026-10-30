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

theorem common_prime_fourth_descent (x y z : Int) (hx : 0<x) (hy : 0<y)
    (hz : 0<z) (he : (x*x)*(x*x)+(y*y)*(y*y)=z*z)
    (p : Nat) (hp : Prime p) (hpx : (p:Int)∣x) (hpy : (p:Int)∣y) :
    ∃ a b c : Int, 0<a ∧ 0<b ∧ 0<c ∧ c<z ∧
      (a*a)*(a*a)+(b*b)*(b*b)=c*c := by
  /-
  Lemma: A common prime factor of the two fourth-power bases yields
  a smaller positive solution. Proof: Write x=p*a and y=p*b. The
  equation implies p divides z*z, so p divides z; write z=p*w.
  Cancel p*p. The resulting equation shows p divides w*w, so w=p*c.
  Cancelling p*p again gives a^4+b^4=c*c. All quotients are positive.
  Since z=p*p*c and p>1, the new last entry c is smaller than z. QED
  -/
  have hp1 : (1:Int)<p := by have := hp.1; omega
  have hpne : (p:Int)≠0 := by omega
  obtain ⟨a,ha⟩ := hpx
  obtain ⟨b,hb⟩ := hpy
  have pos (q r : Int) (hq : 0<q) (hr : q=(p:Int)*r) : 0<r := by
    apply Classical.byContradiction
    intro hh
    have hle := Int.mul_le_mul_of_nonneg_left (show r≤0 by omega) (show (0:Int)≤p by omega)
    simp only [Int.mul_zero] at hle
    omega
  have hapos := pos x a hx ha
  have hbpos := pos y b hy hb
  have norm : (x*x)*(x*x)+(y*y)*(y*y)=
      ((p:Int)*p)*(((p:Int)*p)*((a*a)*(a*a)+(b*b)*(b*b))) := by
    rw [ha,hb,Int.mul_add,Int.mul_add]
    congr 1 <;> ac_rfl
  have hdz : (p:Int)∣z*z := by
    rw [← he,norm]
    exact ⟨(p:Int)*((p:Int)*p)*((a*a)*(a*a)+(b*b)*(b*b)),by ac_rfl⟩
  obtain ⟨w,hw⟩ := (prime_dvd_integer_product p hp z z hdz).elim id id
  have hwpos := pos z w hz hw
  have cancel : ((p:Int)*p)*((a*a)*(a*a)+(b*b)*(b*b))=w*w := by
    apply Int.eq_of_mul_eq_mul_left (a := (p:Int)*p) (Int.mul_ne_zero hpne hpne)
    calc
      ((p:Int)*p)*(((p:Int)*p)*((a*a)*(a*a)+(b*b)*(b*b)))
          = z*z := by rw [← norm]; exact he
      _ = ((p:Int)*p)*(w*w) := by rw [hw]; ac_rfl
  have hdw : (p:Int)∣w*w := by
    rw [← cancel]
    exact ⟨(p:Int)*((a*a)*(a*a)+(b*b)*(b*b)),by ac_rfl⟩
  obtain ⟨c,hc⟩ := (prime_dvd_integer_product p hp w w hdw).elim id id
  have hcpos := pos w c hwpos hc
  have hn : (a*a)*(a*a)+(b*b)*(b*b)=c*c := by
    apply Int.eq_of_mul_eq_mul_left (a := (p:Int)*p) (Int.mul_ne_zero hpne hpne)
    calc
      ((p:Int)*p)*((a*a)*(a*a)+(b*b)*(b*b)) = w*w := cancel
      _ = ((p:Int)*p)*(c*c) := by rw [hc]; ac_rfl
  have hcsmall : c<w := by
    have hh := Int.mul_lt_mul_of_pos_right hp1 hcpos
    simp only [Int.one_mul] at hh
    omega
  have hwsmall : w<z := by
    have hh := Int.mul_lt_mul_of_pos_right hp1 hwpos
    simp only [Int.one_mul] at hh
    omega
  exact ⟨a,b,c,hapos,hbpos,hcpos,by omega,hn⟩

theorem no_fourth_power_square (x y z : Int) (hx : 0<x) (hy : 0<y)
    (hz : 0<z) : ¬ (x^4+y^4=z^2) := by
  /-
  Theorem: The sum of two positive integer fourth powers is not a square.
  Proof: Suppose a solution exists and choose one with least positive
  last entry z. If the bases have a common prime divisor, removing it
  gives a smaller positive solution by the common-prime reduction.
  Otherwise the bases, and therefore their squares, are coprime. The
  square legs form a primitive triangle. Put its even leg first and
  apply the primitive descent to obtain another smaller solution.
  Both alternatives contradict the choice of z. Strong induction on
  the nonnegative integer z expresses this least-counterexample argument.
  Positivity is essential: allowing a zero base would give solutions.
  QED
  -/
  have descent (a b c : Int) (ha : 0<a) (hb : 0<b) (hc : 0<c)
      (he : (a*a)*(a*a)+(b*b)*(b*b)=c*c) :
      ∃ d e f : Int, 0<d ∧ 0<e ∧ 0<f ∧ f<c ∧
        (d*d)*(d*d)+(e*e)*(e*e)=f*f := by
    by_cases hcop : gcd a b=1
    · have hsqcop : gcd (a*a) (b*b)=1 := by
        have hh := coprime_right_product a b b hcop hcop
        exact coprime_product a a (b*b) hh hh
      have htri : Primitive (a*a) (b*b) c := coprime_legs_primitive _ _ _
        ⟨Int.mul_pos ha ha,Int.mul_pos hb hb,hc,he⟩ hsqcop
      rcases even_leg _ _ _ htri.1 with heven | heven
      · exact primitive_fourth_descent a b c ha hb htri heven
      · have hswap : Primitive (b*b) (a*a) c := coprime_legs_primitive _ _ _
          ⟨Int.mul_pos hb hb,Int.mul_pos ha ha,hc,by omega⟩
          (coprime_swap _ _ hsqcop)
        exact primitive_fourth_descent b a c hb ha hswap heven
    · have hex : ∃ p : Nat, Prime p ∧ (p:Int)∣a ∧ (p:Int)∣b := by
        apply Classical.byContradiction
        intro hh
        apply hcop
        apply (coprime_prime_test a b).mpr
        intro p hp hd
        exact hh ⟨p,hp,hd.1,hd.2⟩
      obtain ⟨p,hp,hpa,hpb⟩ := hex
      exact common_prime_fourth_descent a b c ha hb hc he p hp hpa hpb
  have impossible : ∀ n : Nat, ∀ a b c : Int, 0<a → 0<b → 0<c →
      c.natAbs=n → (a*a)*(a*a)+(b*b)*(b*b)=c*c → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro a b c ha hb hc hn he
      obtain ⟨d,e,f,hd,he',hf,hfc,hnorm⟩ := descent a b c ha hb hc he
      have hfcabs : f.natAbs<n := by
        have hca := Int.natAbs_of_nonneg (show 0≤c by omega)
        have hfa := Int.natAbs_of_nonneg (show 0≤f by omega)
        omega
      exact ih f.natAbs hfcabs d e f hd he' hf rfl hnorm
  intro he
  apply impossible z.natAbs x y z hx hy hz rfl
  simpa only [Int.pow_succ,Int.pow_zero,Int.one_mul,Int.mul_one,Int.mul_assoc] using he

end NumberTheory.FourthPowers
