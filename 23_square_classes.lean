import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «06_prime_bounds»
import «09_polynomial_residues»
import «12_modular_powers»
import «13_power_cycles»
import «15_reduced_residues»
import «16_power_recovery»
import «17_polynomial_roots»
import «18_order_counts»
import «19_divisor_counts»
import «20_totient_products»
import «21_modular_roots»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.SquareClasses

open NumberTheory.CommonDivisors (bezout divisor_le_positive gcd)
open NumberTheory.Factorization (Prime prime_divisor)
open NumberTheory.PowerCycles (coprime_not_zero fermat_coprime order_dvd_iff prime_coprime)
open NumberTheory (Congruent modeq_add modeq_mult modeq_pow modeq_refl modeq_symm modeq_trans)
open NumberTheory.ModularPowers (cancel_coprime coprime_power)
open NumberTheory.ModularRoots (primitive_index root_is_coprime)
open NumberTheory.PowerRecovery (power_mul)
open NumberTheory.OrderCounts (PrimitiveRoot monomial monomial_evaluate monomial_leading monomial_length)
open NumberTheory.PolynomialResidues (CompleteResidues Noncongruent evaluate leading)
open NumberTheory.ReducedResidues (factorial phi_prime prime_product_divides wilson)
open NumberTheory.PolynomialRoots (root_count)
open NumberTheory.DivisorCounts (primitive_root_exists)
open NumberTheory.TotientProducts (complete_coprime_count coprimeCount)
open NumberTheory.PrimeBounds (divides_initialProduct initialProduct initialProduct_positive prime_residue_mod_four)


theorem inverse_integer (a : Int) (p : Nat) (hp : Prime p)
    (ha : ¬ (p : Int) ∣ a) : ∃ u : Int, Congruent (a*u) 1 p := by
  /-
  Lemma: An integer not divisible by a prime has an inverse modulo
  that prime. Proof: Bezout gives a*u+p*v=1, since their gcd is one.
  Thus a*u-1=p*(-v), which proves the required congruence. QED
  -/
  rcases bezout a p with ⟨u,v,h⟩
  rw [prime_coprime a p hp ha] at h
  refine ⟨u,by have := hp.1; omega,-v,?_⟩
  rw [Int.mul_neg]
  omega

theorem monic_quadratic (a b c : Int) (p : Nat) (hp : Prime p)
    (ha : ¬ (p : Int) ∣ a) :
    ∃ b' c' : Int, ∀ x : Int,
      Congruent (a*x^2+b*x+c) 0 p ↔ Congruent (x^2+b'*x+c') 0 p := by
  /-
  Theorem: A quadratic with nonzero leading coefficient modulo a
  prime has the same solutions as a monic quadratic.
  Proof: Choose u with a*u congruent to one and put b'=u*b, c'=u*c.
  Multiplying the monic expression by a gives an expression congruent
  to the original quadratic. Cancellation of the coprime factor a
  shows that one is zero exactly when the other is zero. QED
  -/
  rcases inverse_integer a p hp ha with ⟨u,hu⟩
  have hn : 0 < (p : Int) := by have := hp.1; omega
  refine ⟨u*b,u*c,fun x => ?_⟩
  have hb := modeq_mult (a*u) 1 (b*x) (b*x) p hu (modeq_refl _ _ hn)
  have hc := modeq_mult (a*u) 1 c c p hu (modeq_refl _ _ hn)
  have he := modeq_add _ _ _ _ p (modeq_add _ _ _ _ p
    (modeq_refl (a*x^2) p hn) hb) hc
  simp only [Int.one_mul,Int.mul_assoc] at he
  have he' : Congruent (a*(x^2+(u*b)*x+u*c)) (a*x^2+b*x+c) p := by
    simpa only [Int.mul_add,Int.mul_assoc] using he
  constructor
  · intro h
    have hz := modeq_trans _ _ _ p he' h
    apply cancel_coprime _ 0 a p (prime_coprime a p hp ha)
    simpa only [Int.mul_comm,Int.zero_mul,Int.mul_zero] using hz
  · intro h
    have hz := modeq_mult a a _ 0 p (modeq_refl _ _ hn) h
    simp only [Int.mul_zero] at hz
    exact modeq_trans _ _ _ p (modeq_symm _ _ p he') hz

theorem odd_prime_data (p : Nat) (hp : Prime p) (hodd : p % 2=1) :
    0 < (p-1)/2 ∧ p-1=2*((p-1)/2) ∧ ¬ (p : Int) ∣ 2 := by
  /-
  Lemma: For an odd prime, p-1 is twice a positive integer, and
  p does not divide two. Proof: Oddness and p>1 give p>=3.
  Division by two yields p-1=2*((p-1)/2). A positive divisor of
  two is at most two, so p cannot divide two. QED
  -/
  have hp1 := hp.1
  refine ⟨by omega,by omega,?_⟩
  intro h
  have := divisor_le_positive (p : Int) 2 (by omega) h
  omega

theorem complete_square (b c : Int) (p : Nat) (hp : Prime p) (hodd : p % 2=1) :
    ∃ alpha beta : Int, ∀ x : Int,
      Congruent (x^2+b*x+c) 0 p ↔ Congruent ((x+alpha)^2) beta p := by
  /-
  Theorem: Over an odd prime modulus a translation changes a monic
  quadratic equation into a square equation.
  Proof: Invert two modulo p. Choose alpha with 2*alpha congruent
  to b, and put beta=alpha^2-c. Expanding gives
    (x+alpha)^2-beta = x^2+2*alpha*x+c.
  This is congruent to x^2+b*x+c. Hence their being zero is
  equivalent. The odd-prime hypothesis is the approved correction;
  it is needed to invert two. QED
  -/
  rcases inverse_integer 2 p hp (odd_prime_data p hp hodd).2.2 with ⟨u,hu⟩
  have hn : 0 < (p : Int) := by have := hp.1; omega
  let alpha := u*b
  have ha : Congruent (2*alpha) b p := by
    simpa only [alpha,Int.mul_assoc,Int.one_mul] using
      modeq_mult (2*u) 1 b b p hu (modeq_refl _ _ hn)
  refine ⟨alpha,alpha^2-c,fun x => ?_⟩
  have hh := modeq_add _ _ _ _ p
    (modeq_add _ _ _ _ p (modeq_refl (x^2) p hn)
      (modeq_mult _ b x x p ha (modeq_refl _ _ hn)))
    (modeq_refl c p hn)
  have he : (x+alpha)^2-(alpha^2-c)=x^2+(2*alpha)*x+c := by
    simp only [Int.pow_succ,Int.pow_zero,Int.mul_one,Int.one_mul,Int.add_mul,Int.mul_add]
    rw [Int.mul_comm x alpha,Int.mul_assoc 2 alpha x]
    omega
  constructor
  · intro h
    have hz := modeq_trans _ _ _ p hh h
    refine ⟨hn,?_⟩
    rw [he]
    simpa only [Int.sub_zero] using hz.2
  · intro h
    have hz : Congruent (x^2+(2*alpha)*x+c) 0 p := by
      refine ⟨hn,?_⟩
      simpa only [he,Int.sub_zero] using h.2
    exact modeq_trans _ _ _ p (modeq_symm _ _ p hh) hz

def SquareClass (a : Int) (p : Nat) : Prop := ∃ x : Int, Congruent (x^2) a p

theorem square_class_congruent (a b : Int) (p : Nat) (h : Congruent a b p) :
    SquareClass a p ↔ SquareClass b p := by
  /-
  Lemma: Congruent integers are either both squares or both nonsquares.
  Proof: A square congruent to one is congruent to the other by
  transitivity. Use the reverse congruence for the converse. QED
  -/
  constructor
  · rintro ⟨x,hx⟩; exact ⟨x,modeq_trans _ _ _ p hx h⟩
  · rintro ⟨x,hx⟩; exact ⟨x,modeq_trans _ _ _ p hx (modeq_symm _ _ p h)⟩

theorem euler_square_criterion (a : Int) (p : Nat) (hp : Prime p)
    (hodd : p % 2=1) (ha : ¬ (p : Int) ∣ a) :
    SquareClass a p ↔ Congruent (a^((p-1)/2)) 1 p := by
  /-
  Theorem: A nonzero class modulo an odd prime is a square exactly
  when its half-exponent power is one.
  Proof: Put h=(p-1)/2. If a=x^2, then x is coprime to p and
  a^h=x^(2h)=x^(p-1) is one by Fermat.
  Conversely choose a primitive root g and write a congruent to g^i.
  If a^h is one, the order p-1=2h divides i*h. Cancel h to obtain
  2|i. Writing i=2j shows a congruent to (g^j)^2. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hh := odd_prime_data p hp hodd
  have hc := prime_coprime a p hp ha
  constructor
  · rintro ⟨x,hx⟩
    have hxc := root_is_coprime x a p 2 (by decide) hc hx
    have hf := fermat_coprime x p hp hxc
    have he : (x^2)^((p-1)/2)=x^(p-1) := by rw [power_mul,←hh.2.1]
    have ht := modeq_pow _ _ p ((p-1)/2) hx
    rw [he] at ht
    exact modeq_trans _ _ _ p (modeq_symm _ _ p ht) hf
  · intro h
    rcases primitive_root_exists p hp with ⟨g,_hgpos,_hglt,hg⟩
    rcases primitive_index g a p hp hg hc with ⟨e,_he,he⟩
    have ht := modeq_pow _ _ p ((p-1)/2) he
    rw [power_mul] at ht
    have hd := (order_dvd_iff g p hn hg.1 ((e+1)*((p-1)/2))).mp
      (modeq_trans _ _ _ p (modeq_symm _ _ p ht) h)
    rw [hg.2] at hd
    have hd2 : 2*((p-1)/2) ∣ (e+1)*((p-1)/2) := by
      rw [←hh.2.1]
      exact hd
    have hd' : 2 ∣ e+1 := Nat.dvd_of_mul_dvd_mul_right hh.1 hd2
    rcases hd' with ⟨j,hj⟩
    refine ⟨(g : Int)^j,?_⟩
    rw [power_mul,Nat.mul_comm j 2,←hj]
    exact modeq_symm _ _ p he

theorem primitive_power_square (g : Int) (p k : Nat) (hp : Prime p)
    (ho : p%2=1) (hg : PrimitiveRoot g p) :
    SquareClass (g^k) p ↔ 2 ∣ k := by
  /-
  Theorem: A power of a primitive root modulo an odd prime is
  a square exactly when its exponent is even.
  Proof: Put h=(p-1)/2. If g^k is a square, Euler's criterion
  makes g^(k*h) congruent to one. Its order 2h divides k*h,
  and cancellation gives 2|k. Conversely, if k=2j, the power
  is the square of g^j. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hh := odd_prime_data p hp ho
  have hc := coprime_power g p (by omega) hg.1 k
  have ha : ¬ (p : Int) ∣ g^k := by
    intro hd
    exact coprime_not_zero (g^k) p hp.1 hc ⟨by omega,by simpa using hd⟩
  constructor
  · intro hs
    have he := (euler_square_criterion (g^k) p hp ho ha).mp hs
    rw [power_mul] at he
    have hd := (order_dvd_iff g p hn hg.1 (k*((p-1)/2))).mp he
    rw [hg.2] at hd
    have hd2 : 2*((p-1)/2) ∣ k*((p-1)/2) := by
      rw [←hh.2.1]
      exact hd
    exact Nat.dvd_of_mul_dvd_mul_right hh.1 hd2
  · rintro ⟨j,hj⟩
    refine ⟨g^j,?_⟩
    rw [power_mul,Nat.mul_comm j 2,←hj]
    exact modeq_refl _ _ (by omega)

theorem square_one_cases (z : Int) (p : Nat) (hp : Prime p)
    (hz : Congruent (z^2) 1 p) : Congruent z 1 p ∨ Congruent z (-1) p := by
  /-
  Lemma: A square equal to one modulo a prime has base one or minus
  one. Proof: Factor z^2-1=(z-1)*(z+1). A prime dividing this product
  divides one of the factors, giving the two congruences. QED
  -/
  have he : z^2-1=(z-1)*(z+1) := by
    simp only [Int.pow_succ,Int.pow_zero,Int.one_mul,Int.mul_one,
      Int.sub_mul,Int.mul_add,Int.mul_sub,Int.one_mul]
    omega
  have hd := hz.2
  rw [he] at hd
  rcases prime_product_divides p (z-1) (z+1) hp hd with h | h
  · exact Or.inl ⟨hz.1,h⟩
  · exact Or.inr ⟨hz.1,by simpa using h⟩

theorem one_not_neg_one (p : Nat) (hp : Prime p) (hodd : p % 2=1) :
    ¬ Congruent (1 : Int) (-1) p := by
  /-
  Lemma: One and minus one are distinct modulo an odd prime.
  Proof: Otherwise p would divide their difference two. QED
  -/
  intro h
  exact (odd_prime_data p hp hodd).2.2 (by simpa using h.2)

theorem euler_nonsquare_criterion (a : Int) (p : Nat) (hp : Prime p)
    (hodd : p % 2=1) (ha : ¬ (p : Int) ∣ a) :
    ¬ SquareClass a p ↔ Congruent (a^((p-1)/2)) (-1) p := by
  /-
  Theorem: A nonzero class is a nonsquare exactly when its
  half-exponent power is minus one.
  Proof: The square of that power is a^(p-1), which is one.
  Hence the power is one or minus one. The preceding criterion
  associates one precisely with squares, and these two values
  are distinct for an odd prime. QED
  -/
  have hh := odd_prime_data p hp hodd
  have hret : Congruent ((a^((p-1)/2))^2) 1 p := by
    rw [power_mul,Nat.mul_comm _ 2,←hh.2.1]
    exact fermat_coprime a p hp (prime_coprime a p hp ha)
  have hc := euler_square_criterion a p hp hodd ha
  constructor
  · intro hn
    rcases square_one_cases _ p hp hret with h | h
    · exact False.elim (hn (hc.mpr h))
    · exact h
  · intro h hs
    exact one_not_neg_one p hp hodd
      (modeq_trans _ _ _ p (modeq_symm _ _ p (hc.mp hs)) h)

theorem product_power (a b : Int) (k : Nat) : (a*b)^k=a^k*b^k := by
  /-
  Lemma: A power of a product is the product of the powers.
  Proof: At zero both sides are one. In the successor step,
  use the preceding identity and rearrange the factors. QED
  -/
  induction k with
  | zero => simp [Int.pow_zero]
  | succ k ih =>
    rw [Int.pow_succ,ih,Int.pow_succ,Int.pow_succ]
    simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]

theorem nonzero_product (a b : Int) (p : Nat) (hp : Prime p)
    (ha : ¬ (p : Int) ∣ a) (hb : ¬ (p : Int) ∣ b) : ¬ (p : Int) ∣ a*b := by
  /-
  Lemma: The product of two nonzero classes modulo a prime is
  nonzero. Proof: Divisibility of the product would force
  divisibility of one of its factors. QED
  -/
  intro h
  exact (prime_product_divides p a b hp h).elim ha hb

theorem square_times_square (a b : Int) (p : Nat)
    (ha : SquareClass a p) (hb : SquareClass b p) : SquareClass (a*b) p := by
  /-
  Theorem: The product of two square classes is a square class.
  Proof: If x^2 is congruent to a and y^2 to b, then (x*y)^2
  is congruent to a*b, by multiplying the congruences. QED
  -/
  rcases ha with ⟨x,hx⟩
  rcases hb with ⟨y,hy⟩
  exact ⟨x*y,by rw [product_power]; exact modeq_mult _ _ _ _ p hx hy⟩

theorem square_times_nonsquare (a b : Int) (p : Nat) (hp : Prime p)
    (ho : p % 2=1) (ha : ¬ (p : Int) ∣ a) (hb : ¬ (p : Int) ∣ b)
    (hsa : SquareClass a p) (hsb : ¬ SquareClass b p) : ¬ SquareClass (a*b) p := by
  /-
  Theorem: A nonzero square times a nonsquare is a nonsquare.
  Proof: Their half-exponent powers are one and minus one.
  The half-exponent power of their product is therefore minus
  one. Euler's nonsquare criterion proves the assertion. QED
  -/
  apply (euler_nonsquare_criterion (a*b) p hp ho (nonzero_product a b p hp ha hb)).mpr
  rw [product_power]
  have h := modeq_mult _ 1 _ (-1) p
    ((euler_square_criterion a p hp ho ha).mp hsa)
    ((euler_nonsquare_criterion b p hp ho hb).mp hsb)
  simpa only [Int.one_mul] using h

theorem nonsquare_times_nonsquare (a b : Int) (p : Nat) (hp : Prime p)
    (ho : p % 2=1) (ha : ¬ (p : Int) ∣ a) (hb : ¬ (p : Int) ∣ b)
    (hsa : ¬ SquareClass a p) (hsb : ¬ SquareClass b p) : SquareClass (a*b) p := by
  /-
  Theorem: Two nonsquares have a square product modulo an odd prime.
  Proof: Both half-exponent powers are minus one, so their product
  has half-exponent power one. Apply Euler's square criterion. QED
  -/
  apply (euler_square_criterion (a*b) p hp ho (nonzero_product a b p hp ha hb)).mpr
  rw [product_power]
  have h := modeq_mult _ (-1) _ (-1) p
    ((euler_nonsquare_criterion a p hp ho ha).mp hsa)
    ((euler_nonsquare_criterion b p hp ho hb).mp hsb)
  simpa using h

noncomputable def squareSign (a : Int) (p : Nat) : Int :=
  @ite Int (SquareClass a p) (Classical.propDecidable _) 1 (-1)

theorem euler_sign (a : Int) (p : Nat) (hp : Prime p)
    (ho : p % 2=1) (ha : ¬ (p : Int) ∣ a) :
    Congruent (a^((p-1)/2)) (squareSign a p) p := by
  /-
  Theorem: The half-exponent power is congruent to the sign that
  is one for squares and minus one for nonsquares.
  Proof: Split into the square and nonsquare cases and apply
  the corresponding Euler criterion. QED
  -/
  letI : DecidablePred (fun a : Int => SquareClass a p) := fun _ => Classical.propDecidable _
  by_cases hs : SquareClass a p
  · simpa [squareSign,hs] using (euler_square_criterion a p hp ho ha).mp hs
  · simpa [squareSign,hs] using (euler_nonsquare_criterion a p hp ho ha).mp hs

theorem square_sign_product (a b : Int) (p : Nat) (hp : Prime p)
    (ho : p % 2=1) (ha : ¬ (p : Int) ∣ a) (hb : ¬ (p : Int) ∣ b) :
    squareSign (a*b) p=squareSign a p*squareSign b p := by
  /-
  Theorem: The square sign is multiplicative on nonzero classes.
  Proof: There are four cases. Two squares give a square product;
  one square and one nonsquare give a nonsquare product; two
  nonsquares give a square product. These are exactly the four
  multiplication rules for the signs one and minus one. QED
  -/
  letI : DecidablePred (fun a : Int => SquareClass a p) := fun _ => Classical.propDecidable _
  by_cases hs : SquareClass a p <;> by_cases ht : SquareClass b p
  · simp [squareSign,hs,ht,square_times_square a b p hs ht]
  · simp [squareSign,hs,ht,square_times_nonsquare a b p hp ho ha hb hs ht]
  · have h := square_times_nonsquare b a p hp ho hb ha ht hs
    rw [Int.mul_comm b a] at h
    simp [squareSign,hs,ht,h]
  · simp [squareSign,hs,ht,nonsquare_times_nonsquare a b p hp ho ha hb hs ht]

theorem power_value_count (b : Int) (p d : Nat) (hp : Prime p) (hd : 0 < d) (xs : List Int)
    (hpair : xs.Pairwise (fun r s => ¬ Congruent r s p))
    (hroot : ∀ x ∈ xs, Congruent (x^d) b p) : xs.length ≤ d := by
  /-
  Lemma: At most d incongruent integers satisfy x^d=b modulo p.
  Proof: Use the coefficient list [-b,0,...,0,1] for x^d-b.
  It has d+1 coefficients and leading coefficient one, which
  the prime cannot divide. Each given solution is a root of this
  polynomial. The elementary polynomial root bound applies. QED
  -/
  let cs : List Int := -b :: monomial (d-1)
  have hlen : cs.length=d+1 := by simp only [cs,List.length_cons,monomial_length]; omega
  have hlead : leading cs=1 := by
    have hl := monomial_length (d-1)
    cases he : monomial (d-1) with
    | nil => rw [he] at hl; simp at hl
    | cons c tail =>
      change leading (-b::monomial (d-1))=1
      rw [he]
      change leading (c::tail)=1
      rw [← he]
      exact monomial_leading (d-1)
  have hnot : ¬ (p : Int) ∣ leading cs := by
    rw [hlead]
    intro h
    have hb := divisor_le_positive p 1 (by decide) h
    have := hp.1
    omega
  have heval : ∀ x, evaluate cs x=x^d-b := by
    intro x
    change -b+x*evaluate (monomial (d-1)) x=x^d-b
    rw [monomial_evaluate,Int.mul_comm x (x^(d-1)),← Int.pow_succ]
    have he : d-1+1=d := by omega
    rw [he]
    omega
  have hb := root_count cs p hp hnot xs hpair (by
    intro x hx
    rw [heval]
    exact (hroot x hx).2)
  rw [hlen] at hb
  omega

noncomputable def squareEntries (xs : List Int) (p : Nat) : List Int := by
  letI : DecidablePred (fun a : Int => SquareClass a p) := fun _ => Classical.propDecidable _
  exact xs.filter (fun a => decide (¬ (p : Int) ∣ a ∧ SquareClass a p))

noncomputable def nonsquareEntries (xs : List Int) (p : Nat) : List Int := by
  letI : DecidablePred (fun a : Int => SquareClass a p) := fun _ => Classical.propDecidable _
  exact xs.filter (fun a => decide (¬ (p : Int) ∣ a ∧ ¬ SquareClass a p))

noncomputable def nonzeroEntries (xs : List Int) (p : Nat) : List Int :=
  xs.filter (fun a => decide (¬ (p : Int) ∣ a))

theorem square_partition (xs : List Int) (p : Nat) :
    (squareEntries xs p).length+(nonsquareEntries xs p).length=(nonzeroEntries xs p).length := by
  /-
  Lemma: The nonzero entries split into squares and nonsquares.
  Proof: Induct on the list. A zero class enters neither list.
  Every other entry enters exactly one, according to whether
  it is a square. Thus the two counts add to the nonzero count. QED
  -/
  letI : DecidablePred (fun a : Int => SquareClass a p) := fun _ => Classical.propDecidable _
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases hz : (p : Int) ∣ a <;> by_cases hs : SquareClass a p <;>
      simp_all [squareEntries,nonsquareEntries,nonzeroEntries,hz,hs,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem complete_nonzero_count (xs : List Int) (p : Nat) (hp : Prime p)
    (hs : CompleteResidues xs p) : (nonzeroEntries xs p).length=p-1 := by
  /-
  Lemma: A complete residue system modulo a prime has p-1 nonzero
  entries. Proof: An entry is coprime to p exactly when p does
  not divide it. The number of coprime entries in any complete
  system is phi(p), and phi(p)=p-1. QED
  -/
  have he : nonzeroEntries xs p=xs.filter (fun a => decide (gcd a p=1)) := by
    apply List.filter_congr
    intro a _
    have hi : (¬ (p : Int) ∣ a) ↔ gcd a p=1 :=
      ⟨prime_coprime a p hp,fun h hd => coprime_not_zero a p hp.1 h
        ⟨by have := hp.1; omega,by simpa using hd⟩⟩
    simp only [hi]
  rw [he]
  change coprimeCount xs p=p-1
  rw [complete_coprime_count xs p (by have := hp.1; omega) hs,phi_prime p hp]

theorem filtered_noncongruent (xs : List Int) (p : Nat) (h : Noncongruent xs p)
    (f : Int → Bool) : (xs.filter f).Pairwise (fun a b => ¬ Congruent a b p) := by
  /-
  Lemma: Filtering a list of distinct residue classes preserves
  pairwise incongruence. Proof: Filtered entries belong to the
  original list. Congruence would make them equal there, which
  contradicts the preserved absence of repetitions. QED
  -/
  apply List.Pairwise.imp_of_mem ?_ (h.1.filter f)
  intro a b ha hb hab hc
  exact hab (h.2 a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 hc)

theorem half_square_classes (xs : List Int) (p : Nat) (hp : Prime p)
    (ho : p % 2=1) (hs : CompleteResidues xs p) :
    (squareEntries xs p).length=(p-1)/2 ∧
    (nonsquareEntries xs p).length=(p-1)/2 := by
  /-
  Theorem: In any complete residue system modulo an odd prime,
  exactly half of the nonzero entries are squares and half are
  nonsquares. Proof: Put h=(p-1)/2. Euler's criterion places the
  squares among roots of x^h-1 and the nonsquares among roots
  of x^h+1. Each polynomial has degree h and leading coefficient
  one, so each list has at most h entries. The two lists together
  have p-1=2h entries. Both bounds must therefore be equalities.
  QED

  This proves both the perfect-square and quadratic-residue
  formulations. Oddness is required for the approved correction.
  -/
  have hh := odd_prime_data p hp ho
  letI : DecidablePred (fun a : Int => SquareClass a p) := fun _ => Classical.propDecidable _
  have hb := power_value_count 1 p ((p-1)/2) hp hh.1 (squareEntries xs p)
    (filtered_noncongruent xs p hs.1 _) (by
      intro a ha
      have h := List.mem_filter.mp ha
      have hi : ¬ (p : Int) ∣ a ∧ SquareClass a p := of_decide_eq_true h.2
      exact (euler_square_criterion a p hp ho hi.1).mp hi.2)
  have hn := power_value_count (-1) p ((p-1)/2) hp hh.1 (nonsquareEntries xs p)
    (filtered_noncongruent xs p hs.1 _) (by
      intro a ha
      have h := List.mem_filter.mp ha
      have hi : ¬ (p : Int) ∣ a ∧ ¬ SquareClass a p := of_decide_eq_true h.2
      exact (euler_nonsquare_criterion a p hp ho hi.1).mp hi.2)
  have ht := square_partition xs p
  rw [complete_nonzero_count xs p hp hs] at ht
  omega

theorem neg_one_power (k : Nat) :
    (-1 : Int)^k=if k%2=0 then 1 else -1 := by
  /-
  Lemma: Even powers of minus one are one, and odd powers are
  minus one. Proof: The zeroth power is one. Multiplication by
  minus one switches the sign as the parity switches. QED
  -/
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Int.pow_succ,ih]
    by_cases h : k%2=0
    · have h' : (k+1)%2≠0 := by omega
      simp [h,h']
    · have h' : (k+1)%2=0 := by omega
      simp [h,h']

theorem minus_one_square (p : Nat) (hp : Prime p) (ho : p%2=1) :
    SquareClass (-1) p ↔ p%4=1 := by
  /-
  Theorem: Minus one is a square modulo an odd prime exactly
  when the prime has remainder one upon division by four.
  Proof: Euler's criterion tests (-1)^((p-1)/2). This power is
  one precisely when (p-1)/2 is even, equivalently p has
  remainder one modulo four. An odd exponent gives minus one,
  which is distinct from one modulo an odd prime. QED
  -/
  have ha : ¬ (p : Int) ∣ (-1) := by
    intro h
    have hd := Int.dvd_neg.mp h
    have hb := divisor_le_positive (p : Int) 1 (by decide) hd
    have := hp.1
    omega
  rw [euler_square_criterion (-1) p hp ho ha,neg_one_power]
  by_cases he : ((p-1)/2)%2=0
  · have hr : p%4=1 := by have := hp.1; omega
    simp only [if_pos he]
    exact ⟨fun _ => hr,fun _ => modeq_refl 1 p (by have := hp.1; omega)⟩
  · have hr : p%4≠1 := by have := hp.1; omega
    simp only [if_neg he]
    constructor
    · intro h
      exact False.elim (one_not_neg_one p hp ho (modeq_symm _ _ p h))
    · intro h
      exact False.elim (hr h)

theorem minus_one_square_form (p : Nat) (hp : Prime p) (ho : p%2=1) :
    SquareClass (-1) p ↔ ∃ k : Int, (p : Int)=4*k+1 := by
  /-
  Corollary: Minus one is a square exactly when p=4k+1 for an
  integer k. Proof: Division by four identifies remainder one
  with this equation; the quotient supplies k. QED
  -/
  rw [minus_one_square p hp ho]
  constructor
  · intro h
    exact ⟨(p/4 : Nat),by omega⟩
  · rintro ⟨k,hk⟩
    omega

theorem minus_one_sign (p : Nat) (hp : Prime p) (ho : p%2=1) :
    (p%4=1 → squareSign (-1) p=1) ∧ (p%4=3 → squareSign (-1) p= -1) := by
  /-
  Corollary: The sign of minus one is one for primes with remainder
  one modulo four, and minus one for remainder three.
  Proof: Apply the preceding square criterion in the definition
  of the sign. QED
  -/
  constructor
  · intro h
    simp [squareSign,(minus_one_square p hp ho).mpr h]
  · intro h
    have hn : ¬ SquareClass (-1) p := by
      intro hs
      have := (minus_one_square p hp ho).mp hs
      omega
    simp [squareSign,hn]

theorem factorial_reflection (p k : Nat) (hp : 0 < p) (hk : k < p) :
    Congruent (factorial (p-1))
      ((-1 : Int)^k*factorial k*factorial (p-1-k)) p := by
  /-
  Lemma: Removing the top k factors from (p-1)! modulo p gives
    (p-1)! congruent to (-1)^k*k!*(p-1-k)!.
  Proof: Induct on k. Initially no factor is removed. At the next
  step the top remaining factor is p-1-k, congruent to -(k+1).
  Its magnitude extends k! to (k+1)! and its sign contributes
  one more factor of minus one. QED
  -/
  induction k with
  | zero => simpa [factorial,Int.pow_zero] using modeq_refl (factorial (p-1)) p (by omega)
  | succ k ih =>
    have hi := ih (by omega)
    have he : p-1-k=(p-1-(k+1))+1 := by omega
    rw [he,factorial] at hi
    have hfactor : Congruent (((p-1-(k+1))+1 : Nat) : Int) (-((k+1 : Nat) : Int)) p := by
      refine ⟨by omega,1,?_⟩
      simp only [Int.mul_one]
      omega
    have ht := modeq_mult _ _ (factorial (p-1-(k+1))) (factorial (p-1-(k+1))) p
      hfactor (modeq_refl _ _ (by omega))
    have ht' := modeq_mult ((-1 : Int)^k*factorial k) ((-1 : Int)^k*factorial k) _ _ p
      (modeq_refl _ _ (by omega)) ht
    have hf := modeq_trans _ _ _ p hi ht'
    simpa only [factorial,Int.pow_succ,Int.neg_mul,Int.mul_neg,
      Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.one_mul,Int.mul_neg_one] using hf

theorem factorial_square_roots (k p : Nat) (hp : Prime p) (he : p=4*k+1) :
    Congruent ((factorial (2*k))^2) (-1) p ∧
    Congruent ((-factorial (2*k))^2) (-1) p := by
  /-
  Theorem: If p=4k+1 is prime, both (2k)! and its negative square
  to minus one modulo p.
  Proof: Reflect the top 2k factors of (p-1)! using the preceding
  lemma. There are evenly many minus signs, leaving ((2k)!)^2.
  Wilson's theorem makes the original factorial minus one. A
  number and its negative have the same square. QED
  -/
  have hf := factorial_reflection p (2*k) (by have := hp.1; omega) (by omega)
  have hd : p-1-2*k=2*k := by omega
  rw [hd,neg_one_power] at hf
  have hpar : (2*k)%2=0 := by omega
  rw [if_pos hpar,Int.one_mul] at hf
  have hh : Congruent ((factorial (2*k))^2) (-1) p := by
    have h := modeq_trans _ _ _ p (modeq_symm _ _ p hf) (wilson p hp)
    simpa only [Int.pow_succ,Int.pow_zero,Int.one_mul] using h
  refine ⟨hh,?_⟩
  simpa only [Int.pow_succ,Int.pow_zero,Int.one_mul,Int.neg_mul,Int.mul_neg,Int.neg_neg] using hh

theorem prime_one_mod_four_above (n : Nat) :
    ∃ p : Nat, Prime p ∧ n < p ∧ p%4=1 := by
  /-
  Theorem: There are primes congruent to one modulo four above
  every bound, and hence infinitely many such primes.
  Proof: Let M be the product of the positive integers at most n,
  with empty product one, and put N=(2M)^2+1. Choose a prime
  divisor p of N. The number N is odd, so p is odd. The square
  (2M)^2 is minus one modulo p, forcing p to be one modulo four.
  If p were at most n, it would divide M and consequently divide
  both (2M)^2 and (2M)^2+1, forcing it to divide one. This is
  impossible. Thus p exceeds n. QED
  -/
  let M := initialProduct n
  let N := (2*M)*(2*M)+1
  have hmpos : 0 < M := initialProduct_positive n
  have hprod : 0 < (2*M)*(2*M) := Nat.mul_pos (by omega) (by omega)
  rcases prime_divisor N (by dsimp [N]; omega) with ⟨p,hp,hpd⟩
  have hp1 := hp.1
  have hne : p≠2 := by
    intro he
    subst p
    have hd := Nat.mod_eq_zero_of_dvd hpd
    simp [N,Nat.add_mod,Nat.mul_mod] at hd
  have hmod := prime_residue_mod_four p hp hne
  have ho : p%2=1 := by omega
  have hs : SquareClass (-1) p := by
    refine ⟨(2*M : Nat),by omega,?_⟩
    have hd : (p : Int) ∣ (N : Int) := Int.ofNat_dvd.mpr hpd
    simpa only [N,Int.natCast_add,Int.natCast_mul,Int.natCast_one,
      Int.pow_succ,Int.pow_zero,Int.one_mul,Int.sub_neg] using hd
  refine ⟨p,hp,?_,(minus_one_square p hp ho).mp hs⟩
  apply Nat.lt_of_not_ge
  intro hle
  have hm : p ∣ M := divides_initialProduct p n (by omega) hle
  have hz := Nat.mod_eq_zero_of_dvd hm
  have hn := Nat.mod_eq_zero_of_dvd hpd
  have hone : 1%p=1 := Nat.mod_eq_of_lt hp1
  simp [N,Nat.add_mod,Nat.mul_mod,hz,hone] at hn

end NumberTheory.SquareClasses
