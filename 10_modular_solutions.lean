import «01_divisibility»
import «03_common_divisors»
import «09_polynomial_residues»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.List.Nat.Range
import Init.Data.List.Nat.Pairwise
import Lean.Elab.Tactic.Omega

namespace NumberTheory.ModularSolutions

open NumberTheory.CommonDivisors (bezout gcd gcd_positive gcd_quotients linear_solvable_iff)
open NumberTheory.PolynomialResidues (integer_division_exists)
open NumberTheory (Congruent)


theorem linear_congruence_iff_equation (a b n x : Int) (hn : 0 < n) :
    Congruent (a*x) b n ↔ ∃ y : Int, a*x+n*y=b := by
  /-
  Theorem: A solution x of a*x congruent to b modulo n is exactly
  an x that can be extended to a solution of a*x+n*y=b.
  Proof: A congruence gives a*x-b=n*q, so choose y=-q. Conversely,
  a*x+n*y=b gives a*x-b=n*(-y), the divisibility witness. QED
  -/
  constructor
  · rintro ⟨_,q,hq⟩
    exists -q
    rw [Int.mul_neg]
    omega
  · rintro ⟨y,hy⟩
    refine ⟨hn,-y,?_⟩
    rw [Int.mul_neg]
    omega

theorem congruence_solvable_iff (a b n : Int) (hn : 0 < n) :
    (∃ x : Int, Congruent (a*x) b n) ↔ gcd a n ∣ b := by
  /-
  Theorem: The linear congruence a*x congruent to b modulo n has a
  solution exactly when gcd(a,n) divides b.
  Proof: A congruence solution extends to a solution of a*x+n*y=b.
  The integer equation is solvable exactly when its gcd divides b,
  as proved using Bezout coefficients. Conversely, any solution of
  that equation gives a congruence solution by the preceding equivalence.
  QED
  -/
  constructor
  · rintro ⟨x,hx⟩
    rcases (linear_congruence_iff_equation a b n x hn).mp hx with ⟨y,hy⟩
    exact (linear_solvable_iff a n b).mp ⟨x,y,hy⟩
  · intro hd
    rcases (linear_solvable_iff a n b).mpr hd with ⟨x,y,hy⟩
    exact ⟨x,(linear_congruence_iff_equation a b n x hn).mpr ⟨y,hy⟩⟩

theorem modulus_step_data (a n : Int) (hn : 0 < n) :
    0 < gcd a n ∧ 0 < n/gcd a n ∧ n=gcd a n*(n/gcd a n) := by
  /-
  Lemma: For positive n, its gcd d with a is positive, the quotient
  s=n/d is positive, and n=d*s.
  Proof: The inputs are not both zero, so d>0. Divisibility by the
  gcd makes the quotient exact. If s≤0, multiplying by d>0 would
  give n≤0, a contradiction. QED
  -/
  have hd := gcd_positive a n (Or.inr (by omega))
  have he := (gcd_quotients a n).2
  refine ⟨hd,?_,he⟩
  by_cases hs : n/gcd a n ≤ 0
  · have hm := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hd) hs
    rw [←he] at hm
    omega
  · omega

theorem reduced_cross_product (a n : Int) :
    a*(n/gcd a n)=n*(a/gcd a n) := by
  /-
  Lemma: Multiplying a by n/d equals multiplying n by a/d, where
  d=gcd(a,n). Proof: Write a=d*A and n=d*N using exact division.
  Both products are d*A*N, up to reordering the factors. QED
  -/
  have hf := gcd_quotients a n
  calc
    a*(n/gcd a n) = (gcd a n*(a/gcd a n))*(n/gcd a n) :=
      congrArg (fun z => z*(n/gcd a n)) hf.1
    _ = (gcd a n*(n/gcd a n))*(a/gcd a n) := by rw [Int.mul_right_comm]
    _ = n*(a/gcd a n) := congrArg (fun z => z*(a/gcd a n)) hf.2.symm

theorem reduced_modulus_dvd_iff (a n z : Int) (hn : 0 < n) :
    n ∣ a*z ↔ n/gcd a n ∣ z := by
  /-
  Lemma: n divides a*z exactly when n/d divides z, where d=gcd(a,n).
  Proof: Choose a*u+n*v=d. If a*z=n*q, multiplying the Bezout
  equation by z gives d*z=n*(q*u+v*z). Substituting n=d*(n/d)
  and cancelling positive d gives z=(n/d)*(q*u+v*z).
  Conversely, if z=(n/d)*k, the cross-product identity gives
  a*z=n*((a/d)*k), an explicit quotient. QED
  -/
  have hg := modulus_step_data a n hn
  constructor
  · rintro ⟨q,hq⟩
    rcases bezout a n with ⟨u,v,hu⟩
    exists q*u+v*z
    apply Int.eq_of_mul_eq_mul_left (a := gcd a n) (by omega)
    calc
      gcd a n*z = (a*u+n*v)*z := congrArg (fun t => t*z) hu.symm
      _ = (a*z)*u+n*(v*z) := by
        simp only [Int.add_mul,Int.mul_add,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
      _ = n*(q*u+v*z) := by rw [hq,Int.mul_add,Int.mul_assoc]
      _ = gcd a n*((n/gcd a n)*(q*u+v*z)) := by
        calc
          n*(q*u+v*z) = (gcd a n*(n/gcd a n))*(q*u+v*z) :=
            congrArg (fun t => t*(q*u+v*z)) hg.2.2
          _ = _ := by rw [Int.mul_assoc]
  · rintro ⟨k,hk⟩
    exists (a/gcd a n)*k
    calc
      a*z = a*((n/gcd a n)*k) := congrArg (fun t => a*t) hk
      _ = (a*(n/gcd a n))*k := by rw [Int.mul_assoc]
      _ = (n*(a/gcd a n))*k := congrArg (fun t => t*k) (reduced_cross_product a n)
      _ = n*((a/gcd a n)*k) := by rw [Int.mul_assoc]

theorem solution_difference_iff (a b n x₀ x : Int) (hn : 0 < n)
    (h₀ : Congruent (a*x₀) b n) :
    Congruent (a*x) b n ↔ n/gcd a n ∣ x-x₀ := by
  /-
  Theorem: Once x₀ is a solution, x is a solution exactly when
  x-x₀ is divisible by n/gcd(a,n).
  Proof: Subtract the equations a*x-b=n*q and a*x₀-b=n*q₀.
  Their difference says n divides a*(x-x₀). The reduced-modulus
  criterion converts this to divisibility of x-x₀. Conversely,
  that criterion makes a*(x-x₀) a multiple of n; adding the equation
  for x₀ gives an equation proving x is a solution. QED
  -/
  rcases h₀.2 with ⟨q₀,hq₀⟩
  constructor
  · rintro ⟨_,q,hq⟩
    apply (reduced_modulus_dvd_iff a n (x-x₀) hn).mp
    refine ⟨q-q₀,?_⟩
    rw [Int.mul_sub,Int.mul_sub]
    omega
  · intro hd
    rcases (reduced_modulus_dvd_iff a n (x-x₀) hn).mpr hd with ⟨q,hq⟩
    rw [Int.mul_sub] at hq
    refine ⟨hn,q+q₀,?_⟩
    rw [Int.mul_add]
    omega

theorem all_integer_solutions (a b n x₀ x : Int) (hn : 0 < n)
    (h₀ : Congruent (a*x₀) b n) :
    Congruent (a*x) b n ↔ ∃ k : Int, x=x₀+(n/gcd a n)*k := by
  /-
  Corollary: All integer solutions are x₀+(n/d)*k, with k any integer
  and d=gcd(a,n). Proof: The difference criterion says x-x₀=(n/d)*k
  for some integer k. Moving x₀ across the equality gives the formula.
  Conversely, the formula supplies the difference's divisibility witness.
  QED
  -/
  rw [solution_difference_iff a b n x₀ x hn h₀]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,by omega⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,by omega⟩

theorem finite_solution_classes (a b n x₀ x : Int) (hn : 0 < n)
    (h₀ : Congruent (a*x₀) b n) :
    Congruent (a*x) b n ↔ ∃ t : Int, 0 ≤ t ∧ t < gcd a n ∧
      Congruent x (x₀+(n/gcd a n)*t) n := by
  /-
  Theorem: If x₀ is one solution and d=gcd(a,n), every solution is
  congruent modulo n to x₀+(n/d)*t for some t with 0≤t<d.
  Conversely, every integer congruent to one of these is a solution.
  Proof: Put s=n/d. Every solution has the form x=x₀+s*k. Divide
  k by d to write k=d*q+t with 0≤t<d. Since s*d=n, substitution
  gives x=x₀+s*t+n*q, which is the desired congruence. Conversely,
  if x-(x₀+s*t)=n*q, then x-x₀=s*(d*q+t). The difference criterion
  therefore proves that x is a solution. QED
  -/
  have hg := modulus_step_data a n hn
  have hdcast := Int.toNat_of_nonneg (Int.le_of_lt hg.1)
  have hsd : (n/gcd a n)*gcd a n=n := by
    rw [Int.mul_comm]
    exact hg.2.2.symm
  constructor
  · intro hx
    rcases (all_integer_solutions a b n x₀ x hn h₀).mp hx with ⟨k,hk⟩
    rcases integer_division_exists k (gcd a n).toNat (by omega) with
      ⟨q,t,he,ht,htd⟩
    rw [hdcast] at he htd
    have hm : (n/gcd a n)*k=n*q+(n/gcd a n)*t := by
      calc
        (n/gcd a n)*k = (n/gcd a n)*(gcd a n*q+t) :=
          congrArg (fun z => (n/gcd a n)*z) he
        _ = n*q+(n/gcd a n)*t := by rw [Int.mul_add,←Int.mul_assoc,hsd]
    exact ⟨t,ht,htd,hn,q,by omega⟩
  · rintro ⟨t,_,_,_,q,hq⟩
    apply (solution_difference_iff a b n x₀ x hn h₀).mpr
    refine ⟨gcd a n*q+t,?_⟩
    rw [Int.mul_add,←Int.mul_assoc,hsd]
    omega

theorem small_solution_exists (a b n : Int) (hn : 0 < n)
    (hsol : ∃ x : Int, Congruent (a*x) b n) :
    ∃ r : Int, 0 ≤ r ∧ r < n/gcd a n ∧ Congruent (a*r) b n := by
  /-
  Lemma: Whenever there is a solution, there is one between zero
  and n/d-1, where d=gcd(a,n).
  Proof: Choose a solution x and divide it by the positive integer
  s=n/d. Write x=s*q+r with 0≤r<s. Then r-x=s*(-q), so the
  difference criterion shows that r is also a solution. QED
  -/
  rcases hsol with ⟨x,hx⟩
  have hg := modulus_step_data a n hn
  have hscast := Int.toNat_of_nonneg (Int.le_of_lt hg.2.1)
  rcases integer_division_exists x (n/gcd a n).toNat (by omega) with
    ⟨q,r,he,hr,hrs⟩
  rw [hscast] at he hrs
  refine ⟨r,hr,hrs,(solution_difference_iff a b n x r hn hx).mpr ?_⟩
  refine ⟨-q,?_⟩
  rw [Int.mul_neg]
  omega

theorem canonical_progression_solution (a b n r i : Int) (hn : 0 < n)
    (hr : 0 ≤ r) (hrs : r < n/gcd a n) (hsol : Congruent (a*r) b n)
    (hi : 0 ≤ i) (hid : i < gcd a n) :
    0 ≤ r+(n/gcd a n)*i ∧ r+(n/gcd a n)*i < n ∧
      Congruent (a*(r+(n/gcd a n)*i)) b n := by
  /-
  Lemma: Start with a solution r between zero and s-1, where
  d=gcd(a,n) and s=n/d. For each integer i with 0≤i<d, r+s*i
  is a solution between zero and n-1.
  Proof: The term s*i is nonnegative. Also i+1≤d, so
  s*i+s≤s*d=n. Since r<s, we have r+s*i<n. Its difference
  from the known solution r is s*i; the difference criterion
  proves that it is a solution. QED
  -/
  have hg := modulus_step_data a n hn
  have hlo := Int.mul_nonneg (Int.le_of_lt hg.2.1) hi
  have hhi := Int.mul_le_mul_of_nonneg_left (by omega : i+1 ≤ gcd a n)
    (Int.le_of_lt hg.2.1)
  have hsd : (n/gcd a n)*gcd a n=n := by
    rw [Int.mul_comm]
    exact hg.2.2.symm
  rw [Int.mul_add,Int.mul_one,hsd] at hhi
  refine ⟨by omega,by omega,?_⟩
  apply (solution_difference_iff a b n r (r+(n/gcd a n)*i) hn hsol).mpr
  exact ⟨i,by omega⟩

theorem canonical_solution_index (a b n r x : Int) (hn : 0 < n)
    (hr : 0 ≤ r) (hrs : r < n/gcd a n) (hsol : Congruent (a*r) b n) :
    (0 ≤ x ∧ x < n ∧ Congruent (a*x) b n) ↔
      ∃ i : Nat, i < (gcd a n).toNat ∧ x=r+(n/gcd a n)*(i : Int) := by
  /-
  Lemma: With r and s as above, the solutions x between zero and
  n-1 are precisely r+s*i for natural indices i<d.
  Proof: Any solution is r+s*k for an integer k. If k<0, then
  k≤-1 and s*k≤-s, giving x≤r-s<0. If k≥d, then s*k≥s*d=n,
  giving x≥n because r≥0. Thus 0≤k<d, so k is a natural index
  in the stated range. Conversely, each such index gives a
  canonical solution by the bounds and congruence just proved. QED
  -/
  have hg := modulus_step_data a n hn
  have hdcast := Int.toNat_of_nonneg (Int.le_of_lt hg.1)
  have hsd : (n/gcd a n)*gcd a n=n := by
    rw [Int.mul_comm]
    exact hg.2.2.symm
  constructor
  · rintro ⟨hx,hxn,hxs⟩
    rcases (all_integer_solutions a b n r x hn hsol).mp hxs with ⟨k,hk⟩
    have hk0 : 0 ≤ k := by
      by_cases h : k < 0
      · have hm := Int.mul_le_mul_of_nonneg_left (by omega : k ≤ -1)
          (Int.le_of_lt hg.2.1)
        simp only [Int.mul_neg,Int.mul_one] at hm
        omega
      · omega
    have hkd : k < gcd a n := by
      by_cases h : gcd a n ≤ k
      · have hm := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hg.2.1)
        rw [hsd] at hm
        omega
      · omega
    have hkcast := Int.toNat_of_nonneg hk0
    exact ⟨k.toNat,by omega,by rw [hkcast]; exact hk⟩
  · rintro ⟨i,hi,he⟩
    rw [he]
    exact canonical_progression_solution a b n r i hn hr hrs hsol
      (by omega) (by omega)

theorem canonical_solution_count (a b n : Int) (hn : 0 < n)
    (hsol : ∃ x : Int, Congruent (a*x) b n) :
    ∃ solutions : List Int, solutions.Nodup ∧
      solutions.length = (gcd a n).toNat ∧
      ∀ x : Int, x ∈ solutions ↔ 0 ≤ x ∧ x < n ∧ Congruent (a*x) b n := by
  /-
  Theorem: A solvable linear congruence a*x congruent to b modulo n
  has exactly d=gcd(a,n) solutions between zero and n-1.
  Proof: Choose a solution r with 0≤r<s, where s=n/d. Make the
  list r, r+s, ..., r+s*(d-1) by using the indices 0 through d-1.
  The list has d entries. Distinct indices give distinct entries:
  r+s*i=r+s*j implies s*i=s*j, and cancellation of positive s
  gives i=j. The index characterization proves that an integer
  occurs in this list exactly when it is a solution between zero
  and n-1. Thus this list counts every such solution once. QED
  -/
  rcases small_solution_exists a b n hn hsol with ⟨r,hr,hrs,hrsol⟩
  have hg := modulus_step_data a n hn
  let solutions := (List.range (gcd a n).toNat).map
    (fun i : Nat => r+(n/gcd a n)*(i : Int))
  refine ⟨solutions,?_,?_,?_⟩
  · change List.Pairwise (fun x y : Int => x ≠ y)
      ((List.range (gcd a n).toNat).map (fun i : Nat => r+(n/gcd a n)*(i : Int)))
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp (l := List.range (gcd a n).toNat)
      (R := fun i j : Nat => i ≠ j) ?_ (List.nodup_range _)
    intro i j hij he
    have hm : (n/gcd a n)*(i : Int)=(n/gcd a n)*(j : Int) := by omega
    have heq := Int.eq_of_mul_eq_mul_left (a := n/gcd a n) (by omega) hm
    exact hij (by omega)
  · simp only [solutions,List.length_map,List.length_range]
  · intro x
    constructor
    · intro hx
      rcases List.mem_map.mp hx with ⟨i,hi,he⟩
      exact (canonical_solution_index a b n r x hn hr hrs hrsol).mpr
        ⟨i,List.mem_range.mp hi,he.symm⟩
    · intro hx
      rcases (canonical_solution_index a b n r x hn hr hrs hrsol).mp hx with
        ⟨i,hi,he⟩
      exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,he.symm⟩

end NumberTheory.ModularSolutions
