import «01_divisibility»
import «03_common_divisors»
import «04_factorization»
import «09_polynomial_residues»
import «15_reduced_residues»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm
import Lean.Elab.Tactic.Omega

namespace NumberTheory.PolynomialRoots

open NumberTheory.CommonDivisors (dvd_linear)
open NumberTheory (Congruent modeq_symm)
open NumberTheory.Factorization (Prime)
open NumberTheory.ReducedResidues (prime_product_divides)
open NumberTheory.PolynomialResidues (evaluate leading)


def quotient (r : Int) : List Int → List Int
  | [] => []
  | [_] => []
  | _ :: b :: cs => evaluate (b :: cs) r :: quotient r (b :: cs)

theorem division_identity (cs : List Int) (r x : Int) :
    evaluate cs x=(x-r)*evaluate (quotient r cs) x+evaluate cs r := by
  /-
  Lemma: Dividing an integer polynomial f by x-r leaves remainder
  f(r). Coefficient lists run from the constant term upward.
  Proof: Use induction on the coefficient list. Constants have
  zero quotient. Write the next polynomial as a+x*h(x). If
  h(x)=(x-r)*q(x)+h(r), then

    a+x*h(x)=(x-r)*(h(r)+x*q(x))+(a+r*h(r)).

  The last term is f(r), and h(r)+x*q(x) is the quotient given
  by the recursion. All its coefficients are integers. QED
  -/
  induction cs with
  | nil => simp [evaluate,quotient]
  | cons a cs ih =>
    cases cs with
    | nil => simp [evaluate,quotient]
    | cons b cs =>
      change a+x*evaluate (b::cs) x =
        (x-r)*(evaluate (b::cs) r+x*evaluate (quotient r (b::cs)) x)+
          (a+r*evaluate (b::cs) r)
      rw [ih]
      simp only [Int.mul_add,Int.add_mul,Int.sub_mul,Int.mul_sub,
        Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
      omega

theorem quotient_length (cs : List Int) (r : Int) (h : cs ≠ []) :
    (quotient r cs).length+1=cs.length := by
  /-
  Lemma: Dividing a nonempty coefficient list by x-r removes
  exactly one coefficient. Proof: A singleton has empty quotient.
  For a longer list the recursion adds one coefficient to the
  quotient of its tail. Apply induction to that nonempty tail.
  QED
  -/
  induction cs with
  | nil => exact False.elim (h rfl)
  | cons a cs ih =>
    cases cs with
    | nil => rfl
    | cons b cs =>
      have he := ih (by simp)
      simp only [quotient,List.length_cons]
      simp only [List.length_cons] at he
      omega

theorem quotient_leading (cs : List Int) (r : Int) (h : 2 ≤ cs.length) :
    leading (quotient r cs)=leading cs := by
  /-
  Lemma: The quotient of a positive-degree polynomial by x-r has
  the same leading coefficient. Proof: For a linear polynomial,
  the quotient is its leading coefficient. For a longer list,
  both leading coefficients lie in the corresponding tails.
  Apply induction. Thus a nonzero leading coefficient cannot
  disappear in synthetic division. QED
  -/
  induction cs with
  | nil => simp at h
  | cons a cs ih =>
    cases cs with
    | nil => simp at h
    | cons b cs =>
      cases cs with
      | nil => simp [quotient,evaluate,leading]
      | cons c cs =>
        have he := ih (by simp)
        simpa only [quotient,leading] using he

theorem integer_factor (cs : List Int) (r : Int) (hdeg : 2 ≤ cs.length)
    (hl : leading cs ≠ 0) :
    evaluate cs r=0 ↔ ∃ g : List Int,
      g.length+1=cs.length ∧ leading g ≠ 0 ∧
        ∀ x : Int, evaluate cs x=(x-r)*evaluate g x := by
  /-
  Theorem: An integer r is a root of a positive-degree integer
  polynomial exactly when x-r is a factor with integer quotient
  of degree one less. A nonzero final coefficient makes a list
  of length n+1 a polynomial of degree n.
  Proof: If f(r)=0, the division identity has zero remainder.
  The quotient loses one coefficient and keeps the nonzero leading
  coefficient, so its degree is exactly one less. Conversely,
  evaluating a factorization f(x)=(x-r)g(x) at r gives zero. QED
  -/
  constructor
  · intro hr
    refine ⟨quotient r cs,quotient_length cs r (by intro he; subst cs; simp at hdeg),?_,?_⟩
    · rw [quotient_leading cs r hdeg]; exact hl
    · intro x
      have he := division_identity cs r x
      simpa only [hr,Int.add_zero] using he
  · rintro ⟨g,_,_,he⟩
    have h := he r
    simpa only [Int.sub_self,Int.zero_mul] using h

theorem modular_factor (a : Int) (cs : List Int) (r : Int) (p : Nat)
    (hdeg : 1 ≤ cs.length) (hl : leading (a::cs) ≠ 0) (hp : Prime p)
    (hr : Congruent (evaluate (a::cs) r) 0 p) :
    ∃ g : List Int, ∃ b : Int,
      g.length=cs.length ∧ leading g ≠ 0 ∧ Congruent a b p ∧
        ∀ x : Int, evaluate (b::cs) x=(x-r)*evaluate g x := by
  /-
  Theorem: A root modulo p permits division by x-r after changing
  only the constant coefficient to a congruent integer.
  Proof: Take the synthetic quotient g and set b=a-f(r).
  The difference a-b=f(r) is divisible by p. Replacing a by b
  subtracts f(r) from the whole polynomial, so the division
  identity gives (x-r)g(x). The quotient has one fewer coefficient
  and the same nonzero leading coefficient, as required. QED
  -/
  refine ⟨quotient r (a::cs),a-evaluate (a::cs) r,?_,?_,?_,?_⟩
  · have he := quotient_length (a::cs) r (by simp)
    simp only [List.length_cons] at he
    omega
  · rw [quotient_leading (a::cs) r (by simp; omega)]
    exact hl
  · refine ⟨by have := hp.1; omega,?_⟩
    have hd := hr.2
    have he : a-(a-evaluate (a::cs) r)=evaluate (a::cs) r := by omega
    rw [he]
    simpa only [Int.sub_zero] using hd
  · intro x
    have he := division_identity (a::cs) r x
    change a+x*evaluate cs x = _ at he
    change (a-evaluate (a::cs) r)+x*evaluate cs x = _
    omega

theorem quotient_root (cs : List Int) (r s : Int) (p : Nat) (hp : Prime p)
    (hr : (p : Int) ∣ evaluate cs r) (hs : (p : Int) ∣ evaluate cs s)
    (hne : ¬ Congruent r s p) : (p : Int) ∣ evaluate (quotient r cs) s := by
  /-
  Lemma: Removing a root r leaves every incongruent root s as a
  root of the quotient modulo p. Proof: The division identity is

    f(s)-f(r)=(s-r)*g(s).

  The prime divides both values on the left, hence their difference.
  A prime dividing a product divides a factor. It cannot divide
  s-r, since the two roots are incongruent. Therefore it divides
  g(s), as required. QED
  -/
  have hd := dvd_linear p (evaluate cs s) (evaluate cs r) 1 (-1) hs hr
  have he := division_identity cs r s
  have hid : evaluate cs s*1+evaluate cs r*(-1)=(s-r)*evaluate (quotient r cs) s := by
    simp only [Int.mul_one,Int.mul_neg]
    omega
  rw [hid] at hd
  rcases prime_product_divides p (s-r) (evaluate (quotient r cs) s) hp hd with h | h
  · exact False.elim (hne (modeq_symm s r p ⟨by have := hp.1; omega,h⟩))
  · exact h

theorem root_count (cs : List Int) (p : Nat) (hp : Prime p)
    (hl : ¬ (p : Int) ∣ leading cs) (roots : List Int)
    (hdist : roots.Pairwise (fun r s => ¬ Congruent r s p))
    (hroots : ∀ r ∈ roots, (p : Int) ∣ evaluate cs r) :
    roots.length ≤ cs.length-1 := by
  /-
  Lemma: A list of pairwise incongruent roots has at most one
  fewer entries than the coefficient list, provided the prime
  does not divide the leading coefficient.
  Proof: Induct on the length of the coefficient list. An empty
  list has leading coefficient zero, so is excluded. A nonzero
  constant modulo p has no root. Otherwise choose the first root
  r and divide by x-r. Every remaining root is a root of the
  quotient, since it is incongruent to r. The quotient has one
  fewer coefficient and the same leading coefficient. Induction
  bounds the remaining roots by the smaller degree. Restoring r
  adds one and gives the required bound. QED
  -/
  generalize hk : cs.length=k
  induction k using Nat.strongRecOn generalizing cs roots with
  | ind k ih =>
    cases roots with
    | nil => simp
    | cons r rs =>
      have hr := hroots r (by simp)
      have hpair := List.pairwise_cons.mp hdist
      have hdeg : 2 ≤ cs.length := by
        cases cs with
        | nil => exact False.elim (hl ⟨0,by simp [leading]⟩)
        | cons a tail =>
          cases tail with
          | nil =>
            have ha : (p : Int) ∣ a := by simpa [evaluate] using hr
            exact False.elim (hl ha)
          | cons b tail => simp
      have hlen := quotient_length cs r (by intro he; subst cs; simp at hdeg)
      have hlead : ¬ (p : Int) ∣ leading (quotient r cs) := by
        rw [quotient_leading cs r hdeg]
        exact hl
      have hrest : ∀ s ∈ rs, (p : Int) ∣ evaluate (quotient r cs) s := by
        intro s hs
        exact quotient_root cs r s p hp hr (hroots s (by simp [hs])) (hpair.1 s hs)
      have hb := ih (quotient r cs).length (by omega) (quotient r cs) hlead rs hpair.2 hrest rfl
      simp only [List.length_cons]
      omega

theorem polynomial_root_bound (cs : List Int) (n p : Nat) (hp : Prime p)
    (hdegree : cs.length=n+1) (hleading : ¬ (p : Int) ∣ leading cs)
    (roots : List Int) (hdist : roots.Pairwise (fun r s => ¬ Congruent r s p))
    (hroots : ∀ r ∈ roots, Congruent (evaluate cs r) 0 p) : roots.length ≤ n := by
  /-
  Theorem: A degree-n integer polynomial whose leading coefficient
  is not divisible by the prime p has at most n incongruent roots
  modulo p. We express the bound for every finite list of pairwise
  incongruent solutions, so no choice of representatives is needed.
  Proof: Each root congruence says that p divides the polynomial
  value. Apply the coefficient-list root count and substitute
  length=n+1 to obtain the bound n. This includes constant
  polynomials, which have no roots under the stated hypothesis.

  The leading coefficient must be nonzero modulo p, not merely
  nonzero as an integer. Without this hypothesis, the polynomial
  p*x has degree one but every residue class is a root. The
  hypothesis here is the approved correction of that omission.
  QED
  -/
  have h := root_count cs p hp hleading roots hdist (by
    intro r hr
    have hd := (hroots r hr).2
    simpa only [Int.sub_zero] using hd)
  rw [hdegree] at h
  omega

end NumberTheory.PolynomialRoots
