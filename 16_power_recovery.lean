import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «12_modular_powers»
import «13_power_cycles»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PowerRecovery

open NumberTheory.CommonDivisors (bezout gcd)
open NumberTheory (Congruent modeq_mult modeq_pow modeq_refl modeq_symm modeq_trans)
open NumberTheory.PolynomialResidues (bounded_congruent_equal canonicalLabel canonicalLabel_spec)
open NumberTheory.ModularPowers (gcd_one_right power_add)
open NumberTheory.PowerCycles (combine_coprime_moduli fermat_coprime power_multiple_one prime_coprime)
open NumberTheory.Factorization (Prime)


theorem distinct_primes_coprime (p q : Nat) (hp : Prime p) (hq : Prime q)
    (hne : p ≠ q) : gcd (p : Int) q=1 := by
  /-
  Lemma: Distinct primes are relatively prime. Proof: If q divides
  p, primality of p makes q either one or p. Both are excluded.
  The prime coprimality criterion therefore gives gcd(p,q)=1. QED
  -/
  apply prime_coprime p q hq
  intro hd
  have hdn : q ∣ p := Int.ofNat_dvd.mp hd
  rcases hp.2 q hdn with h | h
  · have := hq.1; omega
  · exact hne h.symm

theorem coprime_factor (a n m : Int) (hn : 0 < n) (hc : gcd a (n*m)=1) : gcd a n=1 := by
  /-
  Lemma: Coprimality with a product implies coprimality with either
  factor. Proof: A Bezout identity a*u+(n*m)*v=1 can be written
  a*u+n*(m*v)=1. This identity shows that the gcd with n is one.
  Interchanging the two factors gives the other case. QED
  -/
  rcases bezout a (n*m) with ⟨u,v,he⟩
  rw [hc,Int.mul_assoc] at he
  exact gcd_one_right a n hn ⟨u,m*v,he⟩

theorem two_prime_power_one (W : Int) (p q : Nat) (hp : Prime p) (hq : Prime q)
    (hne : p ≠ q) (hc : gcd W ((p : Int)*q)=1) :
    Congruent (W^((p-1)*(q-1))) 1 ((p : Int)*q) := by
  /-
  Theorem: A number coprime to pq raised to (p-1)(q-1) is one
  modulo pq, for distinct primes p and q. Proof: It is coprime
  to each prime. Fermat's theorem modulo p, raised to the power
  q-1, gives one; the same argument modulo q uses power p-1.
  Since p and q are coprime, the two congruences combine modulo
  pq. The proof permits every integer W, including positive inputs.
  QED
  -/
  have hwp := coprime_factor W p q (by have := hp.1; omega) hc
  have hwq := coprime_factor W q p (by have := hq.1; omega)
    (by simpa only [Int.mul_comm] using hc)
  have h1 := power_multiple_one W p (p-1) (q-1) (fermat_coprime W p hp hwp)
  have h2 := power_multiple_one W q (q-1) (p-1) (fermat_coprime W q hq hwq)
  rw [Nat.mul_comm (q-1) (p-1)] at h2
  exact combine_coprime_moduli _ 1 p q (distinct_primes_coprime p q hp hq hne) h1 h2

theorem prime_shifted_power (W : Int) (p k : Nat) (hp : Prime p) :
    Congruent (W^(1+k*(p-1))) W p := by
  /-
  Lemma: Exponents one greater than a multiple of p-1 return W
  modulo a prime p. Proof: If p divides W, the positive power
  W^(k*(p-1))*W and W are both zero modulo p. Otherwise W is
  coprime to p. Fermat's theorem, raised to power k, makes the
  first factor one modulo p. Multiplying by W proves the claim.
  This also includes k=0 and W=0. QED
  -/
  have hn : 0 < (p : Int) := by have := hp.1; omega
  have he : W^(1+k*(p-1))=W^(k*(p-1))*W := by
    rw [Nat.add_comm,Int.pow_succ]
  rw [he]
  by_cases hd : (p : Int) ∣ W
  · have hz : Congruent W 0 p := ⟨hn,by simpa using hd⟩
    have hm := modeq_mult _ (W^(k*(p-1))) W 0 p (modeq_refl _ _ hn) hz
    simp only [Int.mul_zero] at hm
    exact modeq_trans _ _ _ p hm (modeq_symm _ _ p hz)
  · have hm := power_multiple_one W p (p-1) k (fermat_coprime W p hp (prime_coprime W p hp hd))
    rw [Nat.mul_comm (p-1) k] at hm
    simpa only [Int.one_mul] using modeq_mult _ 1 W W p hm (modeq_refl _ _ hn)

theorem two_prime_power_recovery (W : Int) (p q k : Nat) (hp : Prime p) (hq : Prime q)
    (hne : p ≠ q) : Congruent (W^(1+k*((p-1)*(q-1)))) W ((p : Int)*q) := by
  /-
  Theorem: Raising W to 1+k(p-1)(q-1) returns W modulo pq.
  Proof: The exponent is one plus a multiple of p-1 and also
  one plus a multiple of q-1. Apply the prime shifted-power
  result separately, including when a prime divides W, and
  combine the congruences. No bound on W is needed for this
  congruence; a bound is needed later to recover the exact message.
  QED
  -/
  have h1 := prime_shifted_power W p (k*(q-1)) hp
  have h2 := prime_shifted_power W q (k*(p-1)) hq
  have he1 : (k*(q-1))*(p-1)=k*((p-1)*(q-1)) := by
    rw [Nat.mul_assoc,Nat.mul_comm (q-1) (p-1)]
  rw [he1] at h1
  rw [Nat.mul_assoc] at h2
  exact combine_coprime_moduli _ W p q (distinct_primes_coprime p q hp hq hne) h1 h2

theorem positive_inverse_exponents (E n : Nat) (hE : 0 < E) (hn : 0 < n)
    (hc : gcd (E : Int) n=1) :
    ∃ D y : Nat, 0 < D ∧ 0 < y ∧ E*D=1+y*n := by
  /-
  Lemma: A positive integer E coprime to a positive n admits
  positive D and y with ED=1+yn. Proof: Bezout gives E*u+n*v=1.
  Replace u by its nonnegative representative b modulo n and
  choose D=b+2n. Then D is positive and E*D is congruent to one.
  Write E*D-1=n*y. Since E≥1 and D≥2n≥2, the left side is
  positive, so y is positive as well. Thus both required integers
  can be regarded as positive natural numbers. QED
  -/
  rcases bezout (E : Int) n with ⟨u,v,he⟩
  rw [hc] at he
  let b := canonicalLabel u n
  let D := b+2*n
  have hs := canonicalLabel_spec u n hn
  have hDb : Congruent (D : Int) b n := by
    refine ⟨by omega,2,?_⟩
    dsimp [D]
    simp only [Int.natCast_add,Int.natCast_mul]
    omega
  have hDu := modeq_trans _ _ _ n hDb (modeq_symm _ _ n hs.2)
  have hEu : Congruent ((E : Int)*u) 1 n := by
    refine ⟨by omega,-v,?_⟩
    rw [Int.mul_neg]; omega
  have hED := modeq_trans _ _ _ n
    (modeq_mult E E D u n (modeq_refl _ _ (by omega)) hDu) hEu
  rcases hED.2 with ⟨y,hy⟩
  have hD : 2 ≤ D := by dsimp [D]; omega
  have hbound := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ E)
    (by omega : (0 : Int) ≤ D)
  simp only [Int.one_mul] at hbound
  have hypos : 0 < y := by
    by_cases hy0 : 0 < y
    · exact hy0
    · have hneg := Int.mul_nonneg (by omega : (0 : Int) ≤ n) (by omega : 0 ≤ -y)
      rw [Int.mul_neg] at hneg
      omega
  have hycast : (y.toNat : Int)=y := Int.toNat_of_nonneg (by omega)
  refine ⟨D,y.toNat,by omega,by omega,?_⟩
  have heq : ((E*D : Nat) : Int)=((1+y.toNat*n : Nat) : Int) := by
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_one,hycast]
    rw [Int.mul_comm y (n : Int)]
    omega
  omega

theorem decoding_exponent_exists (p q E : Nat) (hp : Prime p) (hq : Prime q)
    (hE : 0 < E) (hc : gcd (E : Int) ((p-1)*(q-1) : Nat)=1) :
    ∃ D y : Nat, 0 < D ∧ 0 < y ∧ E*D=1+y*((p-1)*(q-1)) := by
  /-
  Theorem: An encoding exponent coprime to (p-1)(q-1) has a
  positive decoding exponent. Proof: Both prime predecessors
  are positive, so their product is positive. Apply the positive
  inverse construction to that product. Distinctness of the
  primes is not needed for this particular existence statement.
  QED
  -/
  have hp1 := hp.1
  have hq1 := hq.1
  exact positive_inverse_exponents E ((p-1)*(q-1)) hE
    (Nat.mul_pos (by omega) (by omega)) hc

theorem exponent_product_recovery (W : Int) (p q E D y : Nat)
    (hp : Prime p) (hq : Prime q) (hne : p ≠ q)
    (hED : E*D=1+y*((p-1)*(q-1))) :
    Congruent (W^(E*D)) W ((p : Int)*q) := by
  /-
  Theorem: The product of encoding and decoding exponents returns
  the original message modulo pq. Proof: Substitute the identity
  ED=1+y(p-1)(q-1) into the two-prime power recovery theorem.
  The result holds even when a prime divides the message. QED
  -/
  rw [hED]
  exact two_prime_power_recovery W p q y hp hq hne

theorem power_mul (a : Int) (i j : Nat) : (a^i)^j=a^(i*j) := by
  /-
  Lemma: Raising a power to another power multiplies exponents.
  Proof: Induct on j. At zero both sides are one. The successor
  multiplies the preceding power by a^i, which adds i to its
  exponent and gives i*(j+1). QED
  -/
  induction j with
  | zero => simp [Int.pow_zero]
  | succ j ih => rw [Int.pow_succ,ih,Nat.mul_succ,power_add]

theorem decode_representative (p q W E D y : Nat) (c : Int)
    (hp : Prime p) (hq : Prime q) (hne : p ≠ q) (hW : W < p*q)
    (hED : E*D=1+y*((p-1)*(q-1)))
    (hc : Congruent c ((W : Int)^E) ((p : Int)*q)) :
    canonicalLabel (c^D) (p*q)=W := by
  /-
  Lemma: Decoding any representative of the encoded power gives
  the original bounded message. Proof: Raise the encoding
  congruence to D. The exponent identity and the recovery theorem
  show that c^D is congruent to W. Its canonical representative
  and W are both between zero and pq-1. Uniqueness of bounded
  representatives therefore makes them equal. QED
  -/
  have hn : 0 < p*q := Nat.mul_pos (by have := hp.1; omega) (by have := hq.1; omega)
  have hm := modeq_pow c ((W : Int)^E) ((p : Int)*q) D hc
  rw [power_mul] at hm
  have hr := modeq_trans _ _ _ ((p : Int)*q) hm (exponent_product_recovery W p q E D y hp hq hne hED)
  have hs := canonicalLabel_spec (c^D) (p*q) hn
  have hr' : Congruent (c^D) W (p*q : Nat) := by simpa only [Int.natCast_mul] using hr
  have he := modeq_trans _ _ _ (p*q : Nat) (modeq_symm _ _ _ hs.2) hr'
  have heq := bounded_congruent_equal (canonicalLabel (c^D) (p*q)) W (p*q : Nat)
    (by omega) (by omega) (by omega) (by omega) he
  omega

theorem decoding_from_factors (p q E : Nat) (hp : Prime p) (hq : Prime q)
    (hne : p ≠ q) (hE : 0 < E) (hc : gcd (E : Int) ((p-1)*(q-1) : Nat)=1) :
    ∃ D : Nat, 0 < D ∧ ∀ W : Nat, W < p*q →
      canonicalLabel (((canonicalLabel ((W : Int)^E) (p*q)) : Int)^D) (p*q)=W := by
  /-
  Theorem: Knowing the two prime factors permits a single decoding
  exponent that recovers every message in range. Proof: From the
  factors, form (p-1)(q-1) and use the Bezout construction to obtain
  positive D and y with ED=1+y(p-1)(q-1). Encode W by taking the
  canonical representative c of W^E modulo pq. By definition c
  is congruent to W^E. The preceding recovery result shows that
  reducing c^D modulo pq gives W itself. The chosen D works for
  every W in the range, including zero and multiples of either
  prime. This verifies the mathematical encoding and decoding
  procedure and explains recovery when the factors are known.
  QED
  -/
  rcases decoding_exponent_exists p q E hp hq hE hc with ⟨D,y,hD,_,hED⟩
  refine ⟨D,hD,?_⟩
  intro W hW
  have hn : 0 < p*q := Nat.mul_pos (by have := hp.1; omega) (by have := hq.1; omega)
  have hs := (canonicalLabel_spec ((W : Int)^E) (p*q) hn).2
  apply decode_representative p q W E D y _ hp hq hne hW hED
  have hs' := modeq_symm _ _ _ hs
  simpa only [Int.natCast_mul] using hs'

end NumberTheory.PowerRecovery
