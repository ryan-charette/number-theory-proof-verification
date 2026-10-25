import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «11_simultaneous_congruences»
import «12_modular_powers»
import «13_power_cycles»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Lean.Elab.Tactic.Omega

namespace NumberTheory.BinomialPowers

open NumberTheory.CommonDivisors (bezout dvd_zero gcd)
open NumberTheory (Congruent dvd_add dvd_mult_of_dvd_left modeq_add modeq_pow modeq_refl modeq_symm modeq_trans)
open NumberTheory.ModularPowers (cancel_coprime gcd_one_right)
open NumberTheory.Factorization (Prime)
open NumberTheory.PowerCycles (small_prime_coprime)
open NumberTheory.SimultaneousCongruences (bezout_product)
open NumberTheory.PolynomialResidues (integer_division_exists)


def coefficient : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, i+1 => coefficient n i+coefficient n (i+1)

theorem coefficient_outside (n i : Nat) (h : n < i) : coefficient n i=0 := by
  /-
  Lemma: Coefficients beyond the end of a row are zero.
  Proof: Induct on the row. In row zero every positive index is
  zero. In the next row, both predecessors of an out-of-range
  index are out of range, so their sum is zero. QED
  -/
  induction n generalizing i with
  | zero => cases i with
    | zero => omega
    | succ i => rfl
  | succ n ih =>
    cases i with
    | zero => omega
    | succ i => simp only [coefficient,ih i (by omega),ih (i+1) (by omega),Int.add_zero]

theorem coefficient_edges (n : Nat) : coefficient n 0=1 ∧ coefficient n n=1 := by
  /-
  Lemma: Both end coefficients of each row are one.
  Proof: The first coefficient is one by definition. Induct on n
  for the last: Pascal's recurrence adds the preceding last
  coefficient to the zero coefficient beyond that row. QED
  -/
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    exact ⟨rfl,by rw [coefficient,ih.2,coefficient_outside n (n+1) (by omega),Int.add_zero]⟩

def factorial : Nat → Int
  | 0 => 1
  | n+1 => (n+1 : Nat)*factorial n

theorem factorial_positive (n : Nat) : 0 < factorial n := by
  /-
  Lemma: Every factorial is positive, including 0!=1.
  Proof: Induct on n. The successor factorial is the preceding
  positive factorial multiplied by the positive integer n+1. QED
  -/
  induction n with
  | zero => decide
  | succ n ih => exact Int.mul_pos (by omega) ih

theorem coefficient_factorial (n i : Nat) (hi : i ≤ n) :
    coefficient n i*factorial i*factorial (n-i)=factorial n := by
  /-
  Lemma: Multiplying a row coefficient by i! and (n-i)! gives n!.
  Proof: Induct on n. The endpoint cases use coefficient one and
  factorial zero equal to one. At an interior position in row n+1,
  expand Pascal's sum. By the induction hypothesis, its two terms
  become (i+1)*n! and (n-i)*n!, whose sum is (n+1)*n!.
  This identity will identify the recursively defined coefficients
  with the factorial quotient from the definition of binomial
  coefficients. QED
  -/
  induction n generalizing i with
  | zero =>
    have he : i=0 := by omega
    subst i
    rfl
  | succ n ih =>
    cases i with
    | zero => simp [coefficient,factorial]
    | succ i =>
      by_cases he : i=n
      · subst i
        rw [(coefficient_edges (n+1)).2,Nat.sub_self,factorial,Int.mul_one,Int.one_mul]
      · have hi' : i+1 ≤ n := by omega
        have h₁ := ih i (by omega)
        have h₂ := ih (i+1) hi'
        have hd : n-i=(n-(i+1))+1 := by omega
        have hf : factorial (n-i)=(n-i : Nat)*factorial (n-(i+1)) := by
          rw [hd,factorial]
        have hsum : ((i+1 : Nat) : Int)+(n-i : Nat)=(n+1 : Nat) := by omega
        rw [coefficient,Nat.succ_sub_succ]
        calc
          (coefficient n i+coefficient n (i+1))*factorial (i+1)*factorial (n-i)
              = ((i+1 : Nat) : Int)*(coefficient n i*factorial i*factorial (n-i))+
                (n-i : Nat)*(coefficient n (i+1)*factorial (i+1)*factorial (n-(i+1))) := by
                  rw [Int.add_mul,Int.add_mul]
                  congr 1
                  · rw [factorial]
                    simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
                  · rw [hf]
                    simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
          _ = ((i+1 : Nat) : Int)*factorial n+(n-i : Nat)*factorial n := by rw [h₁,h₂]
          _ = factorial (n+1) := by rw [←Int.add_mul,hsum,factorial]

theorem coefficient_quotient (n i : Nat) (hi : i ≤ n) :
    coefficient n i=factorial n/(factorial i*factorial (n-i)) := by
  /-
  Theorem: The recursively defined coefficient equals n!/(i!(n-i)!).
  Proof: The denominator is positive. The preceding product identity
  says it divides n! exactly with quotient equal to the coefficient.
  Exact integer division therefore gives the claimed formula. QED
  -/
  have hp := Int.mul_pos (factorial_positive i) (factorial_positive (n-i))
  have he := coefficient_factorial n i hi
  rw [Int.mul_assoc] at he
  rw [←he,Int.mul_ediv_cancel _ (by omega)]

def sumTerms (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => sumTerms f n+f n

theorem sum_congr (f g : Nat → Int) (n : Nat) (h : ∀ i, i < n → f i=g i) :
    sumTerms f n=sumTerms g n := by
  /-
  Lemma: Equal corresponding terms have equal finite sums.
  Proof: Induct on the number of terms, using the hypothesis for
  the final term and induction for all earlier terms. QED
  -/
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTerms,sumTerms,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem sum_linear (f g : Nat → Int) (a b : Int) (n : Nat) :
    sumTerms (fun i => a*f i+b*g i) n=a*sumTerms f n+b*sumTerms g n := by
  /-
  Lemma: A fixed linear combination can be taken outside a finite
  sum. Proof: Induct on its length. The zero case is immediate;
  expand the final terms and distribute multiplication to obtain
  the successor case. QED
  -/
  induction n with
  | zero => simp [sumTerms]
  | succ n ih => simp only [sumTerms,ih,Int.mul_add]; omega

theorem sum_shift (f : Nat → Int) (n : Nat) :
    sumTerms f (n+1)=f 0+sumTerms (fun i => f (i+1)) n := by
  /-
  Lemma: A sum can be split at its first term instead of its last.
  Proof: Induct on the number of terms after the first. In the
  successor step, both sides append the same last term. QED
  -/
  induction n with
  | zero => simp [sumTerms]
  | succ n ih => rw [sumTerms,ih,sumTerms,Int.add_assoc]

def binomialTerm (a b : Int) (n i : Nat) : Int := coefficient n i*a^(n-i)*b^i

theorem term_edges (a b : Int) (n : Nat) :
    binomialTerm a b n 0=a^n ∧ binomialTerm a b n n=b^n ∧
      binomialTerm a b n (n+1)=0 := by
  /-
  Lemma: The endpoint terms are a^n and b^n, and the next term is
  zero. Proof: Use the endpoint coefficients one, the out-of-range
  coefficient zero, and the rule that the zeroth power is one. QED
  -/
  simp only [binomialTerm,(coefficient_edges n).1,(coefficient_edges n).2,
    coefficient_outside n (n+1) (by omega),Nat.sub_zero,Nat.sub_self,
    Int.pow_zero,Int.one_mul,Int.mul_one,Int.zero_mul,and_self]

theorem term_step (a b : Int) (n i : Nat) (hi : i ≤ n) :
    binomialTerm a b (n+1) (i+1)=
      b*binomialTerm a b n i+a*binomialTerm a b n (i+1) := by
  /-
  Lemma: An interior term in the next expansion combines b times
  one old term and a times its successor. Proof: Expand Pascal's
  recurrence and the successor power of b. For i<n, the relevant
  powers of a differ by one, giving the claimed two products.
  At i=n the extra term is zero and the equality is the last-term
  power rule. QED
  -/
  by_cases he : i=n
  · subst i
    rw [(term_edges a b (n+1)).2.1,(term_edges a b n).2.1,
      (term_edges a b n).2.2,Int.mul_zero,Int.add_zero,Int.pow_succ,Int.mul_comm]
  · have hd : n-i=(n-(i+1))+1 := by omega
    have hpow : a^(n-i)=a^(n-(i+1))*a := by rw [hd,Int.pow_succ]
    simp only [binomialTerm,coefficient,Nat.succ_sub_succ,Int.pow_succ]
    rw [hpow]
    simp only [Int.add_mul,Int.mul_add,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]

theorem binomial_expansion (a b : Int) (n : Nat) :
    (a+b)^n=sumTerms (binomialTerm a b n) (n+1) := by
  /-
  Theorem: (a+b)^n is the sum of coefficient(n,i)*a^(n-i)*b^i
  for indices zero through n.
  Proof: Induct on n. At zero both sides are one. Split the next
  sum at its first term and apply the term recurrence to the rest.
  The b-parts give b times the entire old sum. The a-parts give a
  times the old sum without its first term, since the extra last
  term is zero. Restoring the new first term a^(n+1) supplies the
  missing a*a^n. The result is (a+b) times the old sum, exactly
  the successor power. QED
  -/
  induction n with
  | zero => simp [sumTerms,binomialTerm,coefficient,Int.pow_zero]
  | succ n ih =>
    let f := binomialTerm a b n
    have hfirst := (term_edges a b n).1
    have hlast := (term_edges a b n).2.2
    have hshift := sum_shift f n
    have htail : sumTerms (fun i => f (i+1)) (n+1)=sumTerms f (n+1)-a^n := by
      rw [sumTerms]
      change sumTerms (fun i => f (i+1)) n+binomialTerm a b n (n+1)=_
      rw [hlast,Int.add_zero]
      change sumTerms f (n+1)=f 0+sumTerms (fun i => f (i+1)) n at hshift
      have hf : f 0=a^n := hfirst
      rw [hf] at hshift
      omega
    have hterms := sum_congr (fun i => binomialTerm a b (n+1) (i+1))
      (fun i => b*f i+a*f (i+1)) (n+1) (fun i hi => term_step a b n i (by omega))
    rw [sum_shift,(term_edges a b (n+1)).1,hterms,sum_linear,htail]
    change (a+b)^(n+1)=a^(n+1)+(b*sumTerms f (n+1)+a*(sumTerms f (n+1)-a^n))
    have hi' : sumTerms f (n+1)=(a+b)^n := ih.symm
    rw [hi',Int.pow_succ,Int.pow_succ,Int.mul_sub,Int.mul_add]
    rw [Int.mul_comm ((a+b)^n) a,Int.mul_comm ((a+b)^n) b,Int.mul_comm (a^n) a]
    omega

theorem coprime_multiply (a b n : Int) (hn : 0 < n)
    (ha : gcd a n=1) (hb : gcd b n=1) : gcd (a*b) n=1 := by
  /-
  Lemma: Multiplying two integers coprime to n preserves coprimality.
  Proof: Reverse their Bezout identities to put n first, combine
  them by the product identity, then reverse the resulting identity
  to show that a*b and n have gcd one. QED
  -/
  rcases bezout a n with ⟨u,v,hu⟩
  rcases bezout b n with ⟨s,t,hs⟩
  rw [ha] at hu
  rw [hb] at hs
  rcases bezout_product n a b ⟨v,u,by omega⟩ ⟨t,s,by omega⟩ with ⟨x,y,he⟩
  exact gcd_one_right (a*b) n hn ⟨y,x,by omega⟩

theorem factorial_coprime (p k : Nat) (hp : Prime p) (hk : k < p) :
    gcd (factorial k) p=1 := by
  /-
  Lemma: The factorial of an integer below a prime p is coprime
  to p. Proof: Induct on k. The empty product is one. In the
  successor case, k+1 is positive and below p, hence coprime to p;
  multiplying it by the preceding coprime factorial preserves this.
  QED
  -/
  have hn : (0 : Int) < p := by have := hp.1; omega
  induction k with
  | zero => exact gcd_one_right 1 p hn ⟨1,0,by simp⟩
  | succ k ih =>
    exact coprime_multiply (k+1 : Nat) (factorial k) p hn
      (small_prime_coprime p (k+1) hp (by omega) hk) (ih (by omega))

theorem prime_divides_coefficient (p i : Nat) (hp : Prime p)
    (hi : 0 < i) (hip : i < p) : (p : Int) ∣ coefficient p i := by
  /-
  Theorem: A prime divides each interior coefficient in its row.
  Proof: The factorial identity gives C(p,i)*i!*(p-i)!=p!.
  Both denominator factorials are coprime to p because i and p-i
  are below p. Their product can therefore be cancelled modulo p.
  Since p!=p*(p-1)!, the right side is congruent to zero. Cancellation
  leaves C(p,i) congruent to zero, proving divisibility. QED

  The strict bounds exclude both endpoint coefficients, which are
  one. Positivity of i expresses the textbook's natural-number
  convention despite the coefficient definition also allowing zero.
  -/
  have hn : (0 : Int) < p := by have := hp.1; omega
  have hd := coprime_multiply (factorial i) (factorial (p-i)) p hn
    (factorial_coprime p i hp hip) (factorial_coprime p (p-i) hp (by omega))
  have he := coefficient_factorial p i (by omega)
  rw [Int.mul_assoc] at he
  have hp' : p=p-1+1 := by have := hp.1; omega
  have hf : factorial p=(p : Int)*factorial (p-1) := by
    calc
      factorial p=factorial (p-1+1) := congrArg factorial hp'
      _ = (p : Int)*factorial (p-1) := by rw [factorial,←hp']
  have hm : Congruent (coefficient p i*(factorial i*factorial (p-i)))
      (0*(factorial i*factorial (p-i))) p := by
    refine ⟨hn,factorial (p-1),?_⟩
    rw [Int.zero_mul,Int.sub_zero,he,hf]
  have hc := cancel_coprime (coefficient p i) 0 _ p hd hm
  simpa using hc.2

theorem divides_sum (d : Int) (f : Nat → Int) (n : Nat)
    (h : ∀ i, i < n → d ∣ f i) : d ∣ sumTerms f n := by
  /-
  Lemma: A common divisor of all terms divides their finite sum.
  Proof: Induct on the number of terms. Zero is a multiple of d;
  the induction step adds two integers divisible by d. QED
  -/
  induction n with
  | zero => exact dvd_zero d
  | succ n ih => exact dvd_add d _ _ (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem prime_power_sum (a b : Int) (p : Nat) (hp : Prime p) :
    Congruent ((a+b)^p) (a^p+b^p) p := by
  /-
  Theorem: Modulo a prime p, the pth power of a sum is congruent
  to the sum of the pth powers.
  Proof: Expand by the binomial theorem. The first and last terms
  are a^p and b^p. Every interior term contains a coefficient
  divisible by p, so their sum is divisible by p. Subtracting the
  two endpoint terms therefore leaves a multiple of p. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  have hm : (p : Int) ∣ sumTerms (fun i => binomialTerm a b p (i+1)) (p-1) := by
    apply divides_sum
    intro i hi
    have hd := prime_divides_coefficient p (i+1) hp (by omega) (by omega)
    exact dvd_mult_of_dvd_left p _ (b^(i+1))
      (dvd_mult_of_dvd_left p _ (a^(p-(i+1))) hd)
  have hsplit := sum_shift (binomialTerm a b p) (p-1)
  have he : p-1+1=p := by omega
  rw [he,(term_edges a b p).1] at hsplit
  have hex := binomial_expansion a b p
  rw [sumTerms,(term_edges a b p).2.1,hsplit] at hex
  rcases hm with ⟨q,hq⟩
  exact ⟨by omega,q,by omega⟩

theorem one_power (k : Nat) : (1 : Int)^k=1 := by
  /-
  Lemma: Every power of one is one. Proof: At exponent zero this
  is the definition. Each successor multiplies one by one. QED
  -/
  induction k with
  | zero => rfl
  | succ k ih => rw [Int.pow_succ,ih,Int.mul_one]

theorem fermat_natural (a p : Nat) (hp : Prime p) :
    Congruent ((a : Int)^p) a p := by
  /-
  Theorem: For a natural number a and prime p, a^p is congruent
  to a. Proof: Induct on a. At zero, the positive power is zero.
  For the successor use the binomial prime-power congruence to
  replace (a+1)^p by a^p+1. The induction hypothesis replaces a^p
  by a, and adding one gives the desired successor. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  induction a with
  | zero =>
    have he : p=p-1+1 := by omega
    have hz : (0 : Int)^p=0 := by rw [he,Int.pow_succ,Int.mul_zero]
    change Congruent ((0 : Int)^p) 0 p
    rw [hz]
    exact modeq_refl 0 p (by omega)
  | succ a ih =>
    have h := prime_power_sum (a : Int) 1 p hp
    rw [one_power] at h
    have hnext := modeq_add _ _ 1 1 p ih (modeq_refl 1 p (by omega))
    exact modeq_trans _ _ _ p (by simpa using h) (by simpa using hnext)

theorem fermat_integer (a : Int) (p : Nat) (hp : Prime p) :
    Congruent (a^p) a p := by
  /-
  Theorem: For every integer a and prime p, a^p is congruent to a.
  Proof: Divide a by p, obtaining a nonnegative remainder r<p.
  Then a is congruent to r, and raising congruent integers to the
  pth power preserves congruence. The natural-number induction
  just proved gives r^p congruent to r. Combining these congruences
  and reversing a congruent to r gives a^p congruent to a.
  Thus negative inputs follow from the same binomial proof, without
  assuming another version of Fermat's theorem. QED
  -/
  have hn : 0 < p := by have := hp.1; omega
  rcases integer_division_exists a p hn with ⟨q,r,he,hr,_⟩
  have hc : Congruent a r p := ⟨by omega,q,by omega⟩
  have hpow := modeq_pow a r p p hc
  have hnat := fermat_natural r.toNat p hp
  rw [Int.toNat_of_nonneg hr] at hnat
  exact modeq_trans _ _ _ p hpow (modeq_trans _ _ _ p hnat (modeq_symm _ _ p hc))

end NumberTheory.BinomialPowers
