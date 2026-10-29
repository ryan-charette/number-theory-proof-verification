import «27_square_pairs»

namespace NumberTheory.Hypotenuses

open NumberTheory.CommonDivisors
open NumberTheory.Factorization (Prime PrimeFactors product)
open NumberTheory.DivisibilityTests (prime_2 prime_dvd_integer_product)
open NumberTheory.RightTriangles (Primitive)

/- A product in the converse is nonempty: the empty product one cannot
be a hypotenuse of a triple with positive legs. -/

theorem coprime_prime_test (a b : Int) :
    gcd a b=1 ↔ ∀ p : Nat, Prime p → ¬ ((p:Int) ∣ a ∧ (p:Int) ∣ b) := by
  /-
  Lemma: Two integers are coprime exactly when no prime divides both.
  Proof: A common prime divisor divides every linear combination,
  so a Bezout combination equal to one rules it out. Conversely,
  a gcd greater than one has a prime divisor, which divides both
  inputs. A zero gcd makes both inputs zero, so two divides both.
  The only remaining nonnegative gcd is one. QED
  -/
  constructor
  · intro hc p hp hd
    rcases coprime_bezout a b hc with ⟨u,v,huv⟩
    have hh := dvd_linear p a b u v hd.1 hd.2
    rw [huv] at hh
    have := divisor_le_positive p 1 (by decide) hh
    have := hp.1
    omega
  · intro hn
    have hg := gcd_data a b
    by_cases hz : gcd a b=0
    · have ha : a=0 := by rcases hg.2.1 with ⟨u,hu⟩; rw [hz,Int.zero_mul] at hu; exact hu
      have hb : b=0 := by rcases hg.2.2.1 with ⟨v,hv⟩; rw [hz,Int.zero_mul] at hv; exact hv
      exact False.elim (hn 2 prime_2 ⟨ha ▸ dvd_zero 2,hb ▸ dvd_zero 2⟩)
    · by_cases ho : gcd a b=1
      · exact ho
      · have habs := Int.natAbs_of_nonneg hg.1
        have hpos : 1<(gcd a b).natAbs := by omega
        rcases NumberTheory.Factorization.prime_divisor _ hpos with ⟨p,hp,hd⟩
        have hdi : (p:Int) ∣ gcd a b := Int.ofNat_dvd_left.mpr hd
        exact False.elim (hn p hp ⟨Int.dvd_trans hdi hg.2.1,Int.dvd_trans hdi hg.2.2.1⟩)

theorem primitive_hypotenuse_factors (a b c : Int) (h : Primitive a b c) :
    ∃ ps : List Nat, PrimeFactors ps ∧ product ps=c.natAbs ∧
      ∀ p ∈ ps, p%4=1 := by
  /-
  Theorem: A primitive triangle's hypotenuse is a product of primes
  congruent to one modulo four.
  Proof: Factor the positive hypotenuse. It is odd, so two is absent.
  If a prime factor had remainder three modulo four, its divisibility
  into c*c=a*a+b*b would force it to divide both legs. It would then
  be a common divisor of all three sides, contradicting primitivity.
  Every remaining prime has remainder one. QED
  -/
  have hc := h.1.2.2.1
  have hcast : (c.natAbs:Int)=c := Int.natAbs_of_nonneg (by omega)
  rcases NumberTheory.DivisibilityTests.positive_factorization c.natAbs (by omega) with ⟨ps,hps,he⟩
  refine ⟨ps,hps,he,?_⟩
  intro p hp
  have hprime := hps p hp
  have hperm := List.perm_cons_erase hp
  have hf := NumberTheory.Factorization.product_perm _ _ hperm
  rw [he] at hf
  have hdn : p ∣ c.natAbs := ⟨_,hf⟩
  have hd : (p:Int) ∣ c := Int.ofNat_dvd_left.mpr hdn
  have hp2 : p≠2 := by
    intro hh
    subst p
    have hodd := (NumberTheory.RightTriangles.primitive_parity a b c h).2
    omega
  rcases NumberTheory.PrimeBounds.prime_residue_mod_four p hprime hp2 with hh | hh
  · exact hh
  · have hsum : (p:Int) ∣ a*a+b*b := by
      rw [h.1.2.2.2]
      rcases hd with ⟨u,hu⟩
      exact ⟨u*c,by rw [hu,Int.mul_assoc]⟩
    have hab := NumberTheory.SquarePairs.prime_three_divides_roots p hprime hh a b hsum
    have hone := h.2 p (by have := hprime.1; omega) hab.1 hab.2 hd
    have := hprime.1
    omega

theorem multiply_coprime_pair (a b s t : Int) (p : Nat) (hp : Prime p)
    (ho : p%2=1) (hc : gcd a b=1) (he : s*s+t*t=(p:Int))
    (hs : ¬ (p:Int) ∣ s) (ht : ¬ (p:Int) ∣ t) :
    ∃ x y : Int, gcd x y=1 ∧ x*x+y*y=(a*a+b*b)*(p:Int) := by
  /-
  Lemma: Multiplication by an odd prime represented by s*s+t*t can
  preserve coprimality of the roots, provided p divides neither s nor t.
  Proof: Try the two first coordinates a*s+b*t and a*s-b*t. They cannot
  both be divisible by p: adding and subtracting would force p to divide
  a and b, since p divides neither two nor s nor t. Choose the sign
  whose first coordinate is not divisible by p. Put A=a*s+b*t and
  B=b*s-a*t with that choice. If a prime q divided A and B, the identities
  A*s-B*t=a*p and A*t+B*s=b*p show that q divides both a,b unless q=p.
  Coprimality rules out the first case, and the sign choice rules out
  the second. The square-pair multiplication identity gives the norm. QED
  -/
  have build (S T : Int) (hST : S*S+T*T=(p:Int))
      (hA : ¬ (p:Int) ∣ a*S+b*T) :
      ∃ x y : Int, gcd x y=1 ∧ x*x+y*y=(a*a+b*b)*(p:Int) := by
    refine ⟨a*S+b*T,b*S-a*T,?_,?_⟩
    · apply (coprime_prime_test _ _).mpr
      intro q hq hd
      have hqp : q≠p := by intro hh; subst q; exact hA hd.1
      have hnotp : ¬ (q:Int) ∣ (p:Int) := by
        intro hh
        rcases hp.2 q (Int.ofNat_dvd.mp hh) with hh | hh
        · have := hq.1; omega
        · exact hqp hh
      have hda : (q:Int) ∣ a*(p:Int) := by
        have hh := dvd_linear q (a*S+b*T) (b*S-a*T) S (-T) hd.1 hd.2
        have hid : (a*S+b*T)*S+(b*S-a*T)*(-T)=a*(S*S+T*T) := by
          simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,Int.mul_neg,
            Int.neg_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
          omega
        rwa [hid,hST] at hh
      have hdb : (q:Int) ∣ b*(p:Int) := by
        have hh := dvd_linear q (a*S+b*T) (b*S-a*T) T S hd.1 hd.2
        have hid : (a*S+b*T)*T+(b*S-a*T)*S=b*(S*S+T*T) := by
          simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,
            Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
          omega
        rwa [hid,hST] at hh
      have hqa : (q:Int) ∣ a := (prime_dvd_integer_product q hq a p hda).resolve_right hnotp
      have hqb : (q:Int) ∣ b := (prime_dvd_integer_product q hq b p hdb).resolve_right hnotp
      exact (coprime_prime_test a b).mp hc q hq ⟨hqa,hqb⟩
    · rw [← NumberTheory.SquarePairs.square_pair_product_identity,hST]
  by_cases hplus : ¬ (p:Int) ∣ a*s+b*t
  · exact build s t he hplus
  · have hplus' : (p:Int) ∣ a*s+b*t := Classical.not_not.mp hplus
    have hminus : ¬ (p:Int) ∣ a*s-b*t := by
      intro hminus
      have htwo : ¬ (p:Int) ∣ 2 := by
        intro hh
        have := divisor_le_positive p 2 (by decide) hh
        have := hp.1
        omega
      have hpa : (p:Int) ∣ a := by
        have hh := dvd_linear p (a*s+b*t) (a*s-b*t) 1 1 hplus' hminus
        have hid : (a*s+b*t)*1+(a*s-b*t)*1=2*(a*s) := by omega
        rw [hid] at hh
        have hh' := (prime_dvd_integer_product p hp 2 (a*s) hh).resolve_left htwo
        exact (prime_dvd_integer_product p hp a s hh').resolve_right hs
      have hpb : (p:Int) ∣ b := by
        have hh := dvd_linear p (a*s+b*t) (a*s-b*t) 1 (-1) hplus' hminus
        have hid : (a*s+b*t)*1+(a*s-b*t)*(-1)=2*(b*t) := by omega
        rw [hid] at hh
        have hh' := (prime_dvd_integer_product p hp 2 (b*t) hh).resolve_left htwo
        exact (prime_dvd_integer_product p hp b t hh').resolve_right ht
      exact (coprime_prime_test a b).mp hc p hp ⟨hpa,hpb⟩
    apply build s (-t)
    · simpa only [Int.neg_mul_neg] using he
    · simpa only [Int.mul_neg,Int.sub_eq_add_neg] using hminus

theorem coprime_square_product (ps : List Nat) (hps : PrimeFactors ps)
    (hm : ∀ p ∈ ps, p%4=1) :
    ∃ a b : Int, gcd a b=1 ∧ a*a+b*b=(product ps:Int) := by
  /-
  Theorem: A product of primes with remainder one modulo four is a
  sum of two coprime integer squares. Proof: The empty product is
  1 squared plus 0 squared. For each additional prime choose its two
  positive square roots. Both roots are smaller than the prime, so
  neither is divisible by it. The preceding multiplication argument
  extends the representation while preserving coprimality. Induction
  includes repeated prime factors.
  -/
  induction ps with
  | nil =>
    refine ⟨1,0,coprime_of_bezout 1 0 1 0 (by decide), ?_⟩
    rfl
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hfour := hm p (by simp)
    obtain ⟨a,b,hc,he⟩ := ih (fun q hq => hps q (by simp [hq]))
      (fun q hq => hm q (by simp [hq]))
    obtain ⟨s,t,hs,ht,hst⟩ := NumberTheory.SquarePairs.prime_one_square_pair p hp hfour
    have small (u v : Nat) (hu : 0<u) (hv : 0<v) (heq : u*u+v*v=p) :
        ¬ (p:Int) ∣ (u:Int) := by
      have hu1 : 1≤u := by omega
      have hmul := Nat.mul_le_mul_left u hu1
      have hvv := Nat.mul_pos hv hv
      have hup : u<p := by simpa using (show u<p by omega)
      intro hd
      have hle := divisor_le_positive (p:Int) (u:Int) (by omega) hd
      omega
    obtain ⟨x,y,hxy,hn⟩ := multiply_coprime_pair a b s t p hp (by omega) hc
      (by exact_mod_cast hst) (small s t hs ht hst)
      (small t s ht hs (by omega))
    refine ⟨x,y,hxy,?_⟩
    rw [he] at hn
    simpa [product,Int.mul_comm] using hn

theorem coprime_square_hypotenuse (c a b : Int) (hc : 1<c)
    (ho : c%2=1) (hab : gcd a b=1) (he : a*a+b*b=c) :
    ∃ x y : Int, Primitive x y c := by
  /-
  Theorem: An odd integer greater than one that is a sum of coprime
  squares is a primitive hypotenuse. Proof: Replace the roots by their
  absolute values. Neither can be zero: coprimality would force the
  other to be one. Their parities are opposite since their squares
  have odd sum, so they are distinct. Put the larger root first in
  the primitive-triangle parameter construction. Its hypotenuse is
  precisely the original sum of squares.
  -/
  let A : Int := a.natAbs
  let B : Int := b.natAbs
  have hA : 0≤A := by dsimp [A,B]; omega
  have hB : 0≤B := by dsimp [A,B]; omega
  have hcop : gcd A B=1 := NumberTheory.DivisibilityTests.coprime_divisors
    a b A B hab (Int.natAbs_dvd_self) (Int.natAbs_dvd_self)
  have hn : A*A+B*B=c := by
    simpa only [A,B,Int.natAbs_mul_self'] using he
  have pos (u v : Int) (hu : 0≤u) (hv : 0≤v) (hcop : gcd u v=1)
      (hn : u*u+v*v=c) : 0<u := by
    apply Classical.byContradiction
    intro h
    have hz : u=0 := by omega
    obtain ⟨r,s,hrs⟩ := coprime_bezout u v hcop
    have hd : v∣1 := ⟨s, by simpa [hz] using hrs.symm⟩
    have hle := divisor_le_positive v 1 (by decide) hd
    have hv01 : v=0 ∨ v=1 := by omega
    rcases hv01 with hv0 | hv1
    · simp [hz,hv0] at hn; omega
    · simp [hz,hv1] at hn; omega
  have hAp := pos A B hA hB hcop hn
  have hBp := pos B A hB hA (coprime_swap A B hcop) (by omega)
  have hpar : A%2≠B%2 := by
    have ha0 := Int.emod_nonneg A (by decide : (2:Int)≠0)
    have hb0 := Int.emod_nonneg B (by decide : (2:Int)≠0)
    have hrem : (A%2*(A%2)+B%2*(B%2))%2=1 := by
      have hh : (A*A+B*B)%2=1 := by omega
      rw [Int.add_emod,Int.mul_emod A A 2,Int.mul_emod B B 2] at hh
      simpa only [← Int.add_emod] using hh
    have ha : A%2=0 ∨ A%2=1 := by omega
    have hb : B%2=0 ∨ B%2=1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha,hb] at *
  by_cases hlt : B<A
  · refine ⟨2*A*B,A*A-B*B,?_⟩
    simpa only [hn] using NumberTheory.RightTriangles.parameters_primitive A B hBp hlt hcop hpar
  · have hlt' : A<B := by
      have hne : A≠B := fun h => hpar (congrArg (fun z : Int => z%2) h)
      omega
    refine ⟨2*B*A,B*B-A*A,?_⟩
    have hn' : B*B+A*A=c := by omega
    simpa only [hn'] using NumberTheory.RightTriangles.parameters_primitive B A hAp hlt'
      (coprime_swap A B hcop) (Ne.symm hpar)

end NumberTheory.Hypotenuses
