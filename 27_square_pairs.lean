import «26_right_triangles»
import «23_square_classes»

namespace NumberTheory.SquarePairs

open NumberTheory.Factorization (Prime)
open NumberTheory.RightTriangles (square_residue_four)

theorem prime_square_remainder (p : Nat) (hp : Prime p) (a b : Int)
    (he : a*a+b*b=(p:Int)) : p=2 ∨ p%4=1 := by
  /-
  Theorem: A prime expressed as a sum of two integer squares is either
  two or has remainder one modulo four.
  Proof: Each square has remainder zero or one modulo four, so their
  sum cannot have remainder three. If the prime is even, two divides
  it and primality forces it to equal two. Otherwise it is odd, and
  the only remaining remainder modulo four is one. QED
  -/
  have ha := square_residue_four a
  have hb := square_residue_four b
  have hm : (a*a+b*b)%4=(p:Int)%4 := congrArg (fun x : Int => x%4) he
  rw [Int.add_emod] at hm
  by_cases htwo : p%2=0
  · have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero htwo
    rcases hp.2 2 hd with h | h
    · omega
    · exact Or.inl h.symm
  · right
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rw [ha,hb] at hm <;> omega

theorem square_pair_product_identity (a b c d : Int) :
    (a*a+b*b)*(c*c+d*d)=(a*c+b*d)*(a*c+b*d)+(b*c-a*d)*(b*c-a*d) := by
  /-
  Theorem: The product of two sums of squares is a sum of squares:
  (a*a+b*b)*(c*c+d*d)=(a*c+b*d)^2+(b*c-a*d)^2.
  Proof: Expand the right side. The two mixed terms 2*a*b*c*d and
  -2*a*b*c*d cancel. The remaining terms are a*a*c*c, a*a*d*d,
  b*b*c*c, and b*b*d*d, exactly the expansion of the left side. QED
  -/
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

/-
A square pair uses nonnegative integer roots, including zero. Thus a
perfect square is represented by its root and zero. This convention
makes multiplication and the prime-factor criterion valid.
-/
def SquarePair (n : Nat) : Prop := ∃ a b : Nat, a*a+b*b=n

theorem square_pair_integer_iff (n : Nat) :
    SquarePair n ↔ ∃ a b : Int, a*a+b*b=(n:Int) := by
  /-
  Lemma: Allowing integer roots gives exactly the same representations
  as allowing nonnegative roots. Proof: Natural roots are integers.
  Conversely replace each integer root by its absolute value; its
  square is unchanged. QED
  -/
  constructor
  · rintro ⟨a,b,he⟩
    refine ⟨a,b,?_⟩
    exact_mod_cast he
  · rintro ⟨a,b,he⟩
    refine ⟨a.natAbs,b.natAbs,?_⟩
    have hc : ((a.natAbs*a.natAbs+b.natAbs*b.natAbs : Nat) : Int)=(n:Int) := by
      simpa only [Int.natCast_add, Int.natCast_mul, Int.natAbs_mul_self'] using he
    exact Int.ofNat_inj.mp hc

theorem square_pair_mul (m n : Nat) (hm : SquarePair m) (hn : SquarePair n) :
    SquarePair (m*n) := by
  /-
  Theorem: A product of two numbers represented by square pairs has
  a square-pair representation. Proof: Use integer roots a,b and c,d.
  The multiplication identity supplies roots a*c+b*d and b*c-a*d.
  Taking absolute values gives nonnegative roots if necessary. QED
  -/
  rcases (square_pair_integer_iff m).mp hm with ⟨a,b,he⟩
  rcases (square_pair_integer_iff n).mp hn with ⟨c,d,hf⟩
  apply (square_pair_integer_iff (m*n)).mpr
  refine ⟨a*c+b*d,b*c-a*d,?_⟩
  rw [← square_pair_product_identity,he,hf,Int.natCast_mul]

theorem prime_square_window (p : Nat) (hp : Prime p) :
    ∃ m : Nat, 0<m ∧ m<p ∧ m*m<p ∧ p<(m+1)*(m+1) := by
  /-
  Lemma: A prime lies strictly between two consecutive squares.
  Proof: Choose the least k whose square exceeds p, and put m=k-1.
  Minimality gives m*m≤p. Equality would make m a divisor of the
  prime p. The alternatives m=1 and m=p both contradict p=m*m
  and p>1. Thus m*m<p<(m+1)^2, with 0<m<p. QED
  -/
  have hex : ∃ k : Nat, p<k*k := ⟨p+1,by simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega⟩
  rcases NumberTheory.Remainders.least_natural (fun k => p<k*k) hex with ⟨k,hk,hmin⟩
  have hk2 : 1<k := by
    by_cases h0 : k=0
    · simp [h0] at hk
    · by_cases h1 : k=1
      · have := hp.1; simp [h1] at hk; omega
      · omega
  let m := k-1
  have hm : 0<m := by dsimp [m]; omega
  have hkm : k=m+1 := by dsimp [m]; omega
  have hle : m*m≤p := by
    by_cases hh : p<m*m
    · have := hmin m hh; dsimp [m] at this; omega
    · omega
  have hne : m*m≠p := by
    intro he
    rcases hp.2 m ⟨m,he.symm⟩ with h | h
    · rw [h] at he; have := hp.1; omega
    · rw [h] at he
      have hh := Nat.mul_lt_mul_of_pos_left hp.1 (show 0<p by have := hp.1; omega)
      simp only [Nat.mul_one] at hh
      omega
  have hsq : m*m<p := by omega
  exact ⟨m,hm,by have hh := Nat.mul_le_mul_left m (show 1≤m by omega); simp only [Nat.mul_one] at hh; omega,hsq,by simpa [hkm] using hk⟩

theorem small_congruent_pair (p : Nat) (hp : Prime p) (a : Int)
    (ha : ¬ (p:Int) ∣ a) :
    ∃ x y : Int, x≠0 ∧ y≠0 ∧ x*x<(p:Int) ∧ y*y<(p:Int) ∧
      NumberTheory.Congruent (a*x) y p := by
  /-
  Lemma: For a prime p not dividing a, there are nonzero integers x,y
  with a*x congruent to y and both squares smaller than p.
  Proof: Choose m with m*m<p<(m+1)^2. Label the (m+1)^2 pairs
  (q,r), 0≤q,r≤m, by the residue of a*q-r. Two labels coincide.
  Subtract their coordinates to obtain x,y, each between -m and m.
  If x=0, the equal labels force the two r coordinates equal. If y=0,
  cancel a modulo p to force the two q coordinates equal. Either case
  contradicts distinctness of the selected pairs. These bounds prove
  0<|x|,|y|<sqrt(p) without needing real square roots. QED
  -/
  rcases prime_square_window p hp with ⟨m,hm,hmp,hmsq,hlarge⟩
  let k := m+1
  let f := fun i : Nat => NumberTheory.PolynomialResidues.canonicalLabel
    (a*((i/k:Nat):Int)-((i%k:Nat):Int)) p
  have hpp : 0<p := by have := hp.1; omega
  have hf : ∀ i, i<k*k → f i<p := by
    intro i _
    exact (NumberTheory.PolynomialResidues.canonicalLabel_spec _ p hpp).1
  let labels := (List.range (k*k)).map f
  have hlabels : ∀ a ∈ labels, a<p := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨i,hi,rfl⟩
    exact hf i (List.mem_range.mp hi)
  have hlen : labels.length=k*k := by simp [labels]
  rcases NumberTheory.DivisibilityTests.repeated_bounded_label labels p hlabels (by rw [hlen]; exact hlarge) with
    ⟨i,j,hi',hj',hij,he'⟩
  have hi : i<k*k := by omega
  have hj : j<k*k := by omega
  have he : f i=f j := by simpa [labels] using he'
  have hiq : i/k<k := (Nat.div_lt_iff_lt_mul (by dsimp [k]; omega)).mpr hi
  have hjq : j/k<k := (Nat.div_lt_iff_lt_mul (by dsimp [k]; omega)).mpr hj
  have hir : i%k<k := Nat.mod_lt i (by dsimp [k]; omega)
  have hjr : j%k<k := Nat.mod_lt j (by dsimp [k]; omega)
  let q : Int := (i/k:Nat)
  let Q : Int := (j/k:Nat)
  let r : Int := (i%k:Nat)
  let R : Int := (j%k:Nat)
  have qb : 0≤q ∧ q≤m := by
    constructor
    · exact Int.ofNat_zero_le _
    · dsimp only [q]
      exact_mod_cast (show i/k≤m by dsimp [k] at hiq ⊢; omega)
  have Qb : 0≤Q ∧ Q≤m := by
    constructor
    · exact Int.ofNat_zero_le _
    · dsimp only [Q]
      exact_mod_cast (show j/k≤m by dsimp [k] at hjq ⊢; omega)
  have rb : 0≤r ∧ r≤m := by dsimp [r]; omega
  have Rb : 0≤R ∧ R≤m := by dsimp [R]; omega
  have hdiff : q≠Q ∨ r≠R := by
    apply Classical.byContradiction
    intro hh
    have hq : i/k=j/k := by
      have hh' : q=Q := by omega
      exact Int.ofNat_inj.mp hh'
    have hr : i%k=j%k := by
      have hh' : r=R := by omega
      exact Int.ofNat_inj.mp hh'
    have hi' := Nat.mod_add_div i k
    have hj' := Nat.mod_add_div j k
    rw [hq,hr] at hi'
    omega
  have hc : NumberTheory.Congruent (a*q-r) (a*Q-R) p :=
    (NumberTheory.PolynomialResidues.canonicalLabel_eq_iff _ _ p hpp).mp he
  have hxy : NumberTheory.Congruent (a*(q-Q)) (r-R) p := by
    refine ⟨hc.1,?_⟩
    have heq : a*(q-Q)-(r-R)=(a*q-r)-(a*Q-R) := by rw [Int.mul_sub]; omega
    rw [heq]
    exact hc.2
  have hx : q-Q≠0 := by
    intro hz
    have hd : (p:Int) ∣ r-R := by
      have hd := hxy.2
      rw [hz,Int.mul_zero,Int.zero_sub] at hd
      exact Int.dvd_neg.mp hd
    have hr := NumberTheory.PolynomialResidues.bounded_congruent_equal r R p
      rb.1 (by omega) Rb.1 (by omega) ⟨by omega,hd⟩
    omega
  have hy : r-R≠0 := by
    intro hz
    have hd := hxy.2
    rw [hz,Int.sub_zero] at hd
    have hcop := NumberTheory.DivisibilityTests.prime_not_dvd_iff_coprime p hp a |>.mp ha
    have hd' := NumberTheory.CommonDivisors.coprime_dvd_cancel p a (q-Q) hd
      (NumberTheory.CommonDivisors.coprime_swap a p hcop)
    have hq := NumberTheory.PolynomialResidues.bounded_congruent_equal q Q p
      qb.1 (by omega) Qb.1 (by omega) ⟨by omega,hd'⟩
    omega
  have square_bound (z : Int) (hz : -(m:Int)≤z ∧ z≤m) : z*z<(p:Int) := by
    by_cases hpos : 0≤z
    · have := Int.mul_self_le_mul_self hpos hz.2
      omega
    · have hh := Int.mul_self_le_mul_self (show 0≤-z by omega) (show -z≤m by omega)
      simp only [Int.neg_mul_neg] at hh
      omega
  exact ⟨q-Q,r-R,hx,hy,square_bound _ (by omega),square_bound _ (by omega),hxy⟩

theorem prime_one_square_pair (p : Nat) (hp : Prime p) (hfour : p%4=1) :
    ∃ u v : Nat, 0<u ∧ 0<v ∧ u*u+v*v=p := by
  /-
  Theorem: A prime with remainder one modulo four is the sum of two
  positive squares. Proof: Earlier work supplies a square root a of
  minus one modulo p. It is not divisible by p. Choose the small
  nonzero pair x,y with a*x congruent to y. Squaring gives
  y*y congruent to -x*x, so p divides x*x+y*y. This positive sum is
  smaller than 2*p because each square is smaller than p. It must
  therefore equal p. Absolute values give positive natural roots. QED
  -/
  have ho : p%2=1 := by omega
  rcases (NumberTheory.SquareClasses.minus_one_square p hp ho).mpr hfour with ⟨a,hr⟩
  have hpp : 0<(p:Int) := by have := hp.1; omega
  have ha : ¬ (p:Int) ∣ a := by
    intro hd
    have hs : (p:Int) ∣ a^2 := by
      rcases hd with ⟨k,hk⟩
      refine ⟨k*a,?_⟩
      simp only [Int.pow_succ,Int.pow_zero,Int.mul_one,Int.one_mul]
      rw [hk,Int.mul_assoc]
    have hone := NumberTheory.CommonDivisors.dvd_linear p (a^2-(-1)) (a^2) 1 (-1) hr.2 hs
    have he : (a^2-(-1))*1+a^2*(-1)=1 := by omega
    rw [he] at hone
    have := NumberTheory.CommonDivisors.divisor_le_positive p 1 (by decide) hone
    have := hp.1
    omega
  rcases small_congruent_pair p hp a ha with ⟨x,y,hx,hy,hxx,hyy,hxy⟩
  have h1 := NumberTheory.modeq_square (a*x) y p hxy
  have h2 := NumberTheory.modeq_mult (a^2) (-1) (x^2) (x^2) p hr
    (NumberTheory.modeq_refl (x^2) p hpp)
  have hd : (p:Int) ∣ x*x+y*y := by
    have hh := NumberTheory.CommonDivisors.dvd_linear p ((a*x)^2-y^2)
      (a^2*x^2-(-1)*x^2) (-1) 1 h1.2 h2.2
    have he : ((a*x)^2-y^2)*(-1)+(a^2*x^2-(-1)*x^2)*1=x*x+y*y := by
      simp only [Int.pow_succ,Int.pow_zero,Int.mul_one,Int.one_mul,
        Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,Int.mul_neg,
        Int.neg_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
      omega
    rwa [he] at hh
  have positive_square (z : Int) (hz : z≠0) : 0<z*z := by
    by_cases hh : 0<z
    · exact Int.mul_pos hh hh
    · have hh' : 0 < -z := by omega
      simpa only [Int.neg_mul_neg] using Int.mul_pos hh' hh'
  have hxpos := positive_square x hx
  have hypos := positive_square y hy
  have hle := NumberTheory.CommonDivisors.divisor_le_positive p (x*x+y*y) (by omega) hd
  have hsmall : NumberTheory.Congruent (x*x+y*y-(p:Int)) 0 p := by
    refine ⟨hpp,?_⟩
    simp only [Int.sub_zero]
    exact Int.dvd_sub hd (NumberTheory.CommonDivisors.dvd_refl p)
  have he := NumberTheory.PolynomialResidues.bounded_congruent_equal
    (x*x+y*y-(p:Int)) 0 p (by omega) (by omega) (by omega) hpp hsmall
  refine ⟨x.natAbs,y.natAbs,Int.natAbs_pos.mpr hx,Int.natAbs_pos.mpr hy,?_⟩
  have heq : x*x+y*y=(p:Int) := by omega
  have hc : ((x.natAbs*x.natAbs+y.natAbs*y.natAbs:Nat):Int)=(p:Int) := by
    simpa only [Int.natCast_add,Int.natCast_mul,Int.natAbs_mul_self'] using heq
  exact Int.ofNat_inj.mp hc

theorem prime_square_pair_iff (p : Nat) (hp : Prime p) :
    SquarePair p ↔ p=2 ∨ p%4=1 := by
  /-
  Theorem: A prime is a sum of two nonnegative squares precisely when
  it is two or has remainder one modulo four.
  Proof: The residue restriction gives necessity. For two use 1,1.
  For remainder one use the positive roots constructed above. QED
  -/
  constructor
  · intro h
    rcases (square_pair_integer_iff p).mp h with ⟨a,b,he⟩
    exact prime_square_remainder p hp a b he
  · intro h
    rcases h with h | h
    · subst p
      exact ⟨1,1,rfl⟩
    · rcases prime_one_square_pair p hp h with ⟨a,b,_ha,_hb,he⟩
      exact ⟨a,b,he⟩

theorem prime_three_divides_roots (p : Nat) (hp : Prime p) (hthree : p%4=3)
    (a b : Int) (hd : (p:Int) ∣ a*a+b*b) : (p:Int) ∣ a ∧ (p:Int) ∣ b := by
  /-
  Lemma: If a prime congruent to three modulo four divides a sum of
  squares, it divides both roots.
  Proof: Suppose it does not divide b. Invert b modulo p, writing
  b*u congruent to one. Multiplying the square sum by u*u shows that
  (a*u)^2 is congruent to minus one. But minus one is not a square
  for this prime. Therefore p divides b. Subtract b*b from the sum;
  p divides a*a, and prime divisibility of a product gives p divides a. QED
  -/
  have hb : (p:Int) ∣ b := by
    apply Classical.byContradiction
    intro hn
    rcases NumberTheory.SquareClasses.inverse_integer b p hp hn with ⟨u,hu⟩
    have hs := NumberTheory.modeq_square (b*u) 1 p hu
    have hm : (p:Int) ∣ (a*a+b*b)*(u*u) := by
      rcases hd with ⟨k,hk⟩
      exact ⟨k*(u*u),by rw [hk,Int.mul_assoc]⟩
    have hroot : NumberTheory.SquareClasses.SquareClass (-1) p := by
      refine ⟨a*u,hu.1,?_⟩
      have hh := NumberTheory.CommonDivisors.dvd_linear p ((a*a+b*b)*(u*u))
        ((b*u)^2-1^2) 1 (-1) hm hs.2
      have he : ((a*a+b*b)*(u*u))*1+((b*u)^2-1^2)*(-1)=(a*u)^2-(-1) := by
        simp only [Int.pow_succ,Int.pow_zero,Int.mul_one,Int.one_mul,
          Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,Int.mul_neg,
          Int.neg_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
        omega
      rwa [he] at hh
    have := (NumberTheory.SquareClasses.minus_one_square p hp (by omega)).mp hroot
    omega
  have hbb : (p:Int) ∣ b*b := by
    rcases hb with ⟨k,hk⟩
    exact ⟨k*b,by rw [hk,Int.mul_assoc]⟩
  have haa : (p:Int) ∣ a*a := by
    have hh := Int.dvd_sub hd hbb
    simpa only [Int.add_sub_cancel] using hh
  have ha := NumberTheory.DivisibilityTests.prime_dvd_integer_product p hp a a haa
  exact ⟨ha.elim id id,hb⟩

theorem prime_exponent_self (p : Nat) (hp : Prime p) :
    NumberTheory.DivisibilityTests.exponent p p=1 := by
  /-
  Lemma: A prime occurs exactly once in its own prime factorization.
  Proof: The one-entry list containing p is a prime factorization of p.
  Independence of the chosen factor list makes its count equal to one. QED
  -/
  rw [NumberTheory.DivisibilityTests.exponent_of_factors p p (by have := hp.1; omega)
    [p] (by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact hp)
    (by simp [NumberTheory.Factorization.product])]
  simp

theorem absent_prime_exponent (p n : Nat) (hn : 0<n) (hd : ¬p ∣ n) :
    NumberTheory.DivisibilityTests.exponent p n=0 := by
  /-
  Lemma: A number that does not divide n cannot appear in its prime
  factor list. Proof: If it appeared, separate that occurrence from
  the product to see that it divides n. Thus its occurrence count is zero. QED
  -/
  have hf := NumberTheory.DivisibilityTests.factors_spec n hn
  have hnot : p ∉ NumberTheory.DivisibilityTests.factors n := by
    intro hm
    have hperm := List.perm_cons_erase hm
    have he := NumberTheory.Factorization.product_perm _ _ hperm
    rw [hf.2] at he
    apply hd
    exact ⟨_,he⟩
  exact List.count_eq_zero.mpr hnot

end NumberTheory.SquarePairs
