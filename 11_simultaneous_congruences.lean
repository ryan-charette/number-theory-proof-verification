import «01_divisibility»
import «03_common_divisors»
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.DivModLemmas
import Init.Data.List.Pairwise
import Lean.Elab.Tactic.Omega

namespace NumberTheory.SimultaneousCongruences

open NumberTheory.CommonDivisors (bezout divisor_le_positive dvd_linear gcd gcd_data gcd_positive linear_solvable_iff)
open NumberTheory (Congruent)


theorem two_congruences_solvable (a b n m : Int) (hn : 0 < n) (hm : 0 < m) :
    (∃ x : Int, Congruent x a n ∧ Congruent x b m) ↔ gcd n m ∣ a-b := by
  /-
  Theorem: Two prescribed remainders a modulo n and b modulo m
  can occur together exactly when gcd(n,m) divides a-b.
  Proof: A common solution gives x-a=n*u and x-b=m*v, hence
  a-b=n*(-u)+m*v. The integer-equation criterion gives necessity.
  Conversely, that criterion supplies n*u+m*v=a-b. Set x=a-n*u.
  Then x-a=n*(-u) and x-b=m*v, proving both congruences. QED
  -/
  constructor
  · rintro ⟨x,⟨_,u,hu⟩,⟨_,v,hv⟩⟩
    apply (linear_solvable_iff n m (a-b)).mp
    refine ⟨-u,v,?_⟩
    rw [Int.mul_neg]
    omega
  · intro hd
    rcases (linear_solvable_iff n m (a-b)).mpr hd with ⟨u,v,he⟩
    refine ⟨a-n*u,⟨hn,-u,?_⟩,⟨hm,v,?_⟩⟩
    · rw [Int.mul_neg]; omega
    · omega

theorem congruence_from_solution (x a r n : Int) (hr : Congruent r a n) :
    Congruent x a n ↔ n ∣ x-r := by
  /-
  Lemma: If r has remainder a modulo n, then x has that same
  remainder exactly when n divides x-r.
  Proof: Subtract the multiple equations for x-a and r-a to
  obtain one for x-r. Conversely, add an equation for x-r to
  the one for r-a to recover the equation for x-a. QED
  -/
  rcases hr with ⟨hn,q,hq⟩
  constructor
  · rintro ⟨_,p,hp⟩
    refine ⟨p-q,?_⟩
    rw [Int.mul_sub]; omega
  · rintro ⟨p,hp⟩
    refine ⟨hn,p+q,?_⟩
    rw [Int.mul_add]; omega

theorem product_divides (n m z : Int)
    (hcop : ∃ u v : Int, n*u+m*v=1) :
    (n ∣ z ∧ m ∣ z) ↔ n*m ∣ z := by
  /-
  Lemma: If n and m have a linear combination equal to one, their
  product divides z exactly when each of them divides z.
  Proof: Write z=n*i=m*j and n*u+m*v=1. Multiplication gives
  z=z*(n*u+m*v)=n*m*(j*u+i*v). This is a product-divisibility
  witness. Conversely, z=n*m*k exhibits factors n and m separately.
  QED
  -/
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    rcases hcop with ⟨u,v,he⟩
    refine ⟨j*u+i*v,?_⟩
    have h₁ : z*(n*u)=(n*m)*(j*u) := by
      rw [hj]
      simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    have h₂ : z*(m*v)=(n*m)*(i*v) := by
      rw [hi]
      simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    calc
      z = z*1 := by rw [Int.mul_one]
      _ = z*(n*u+m*v) := congrArg (fun t => z*t) he.symm
      _ = (n*m)*(j*u+i*v) := by rw [Int.mul_add,h₁,h₂,Int.mul_add]
  · rintro ⟨k,hk⟩
    constructor
    · exact ⟨m*k,by rw [hk,Int.mul_assoc]⟩
    · refine ⟨n*k,?_⟩
      rw [hk]
      simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]

theorem two_coprime_congruences (a b n m : Int) (hn : 0 < n) (hm : 0 < m)
    (hcop : gcd n m=1) :
    ∃ r : Int, ∀ x : Int,
      (Congruent x a n ∧ Congruent x b m) ↔ Congruent x r (n*m) := by
  /-
  Theorem: For relatively prime positive moduli, two congruences
  specify exactly one congruence class modulo their product.
  Proof: Their gcd is one, which divides a-b, so choose a common
  solution r. An integer x solves both congruences exactly when
  both moduli divide x-r. Bezout coefficients for their gcd give
  a linear combination equal to one. The product-divisibility
  lemma therefore makes this equivalent to n*m dividing x-r.
  This also proves uniqueness modulo n*m. QED
  -/
  have hd : gcd n m ∣ a-b := by
    rw [hcop]; exact ⟨a-b,by rw [Int.one_mul]⟩
  rcases (two_congruences_solvable a b n m hn hm).mpr hd with ⟨r,hrn,hrm⟩
  have hb := bezout n m
  rw [hcop] at hb
  refine ⟨r,?_⟩
  intro x
  rw [congruence_from_solution x a r n hrn,congruence_from_solution x b r m hrm]
  constructor
  · intro h
    exact ⟨Int.mul_pos hn hm,(product_divides n m (x-r) hb).mp h⟩
  · intro h
    exact (product_divides n m (x-r) hb).mpr h.2

theorem bezout_product (a b c : Int)
    (hb : ∃ u v : Int, a*u+b*v=1) (hc : ∃ u v : Int, a*u+c*v=1) :
    ∃ u v : Int, a*u+(b*c)*v=1 := by
  /-
  Lemma: If a has a linear combination equal to one with each of
  b and c, it also has one with b*c.
  Proof: Write a*u+b*v=1 and a*p+c*q=1. Multiply the second
  equality by b*v and substitute for b*v in the first. We obtain
  a*(u+b*v*p)+(b*c)*(v*q)=1. These are the required coefficients.
  QED
  -/
  rcases hb with ⟨u,v,hu⟩
  rcases hc with ⟨p,q,hp⟩
  refine ⟨u+b*v*p,v*q,?_⟩
  have he := congrArg (fun t => t*(b*v)) hp
  simp only [Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_assoc,
    Int.mul_left_comm,Int.mul_comm,Int.mul_one] at he ⊢
  omega

theorem gcd_one_of_bezout (a b : Int) (ha : 0 < a)
    (h : ∃ u v : Int, a*u+b*v=1) : gcd a b=1 := by
  /-
  Lemma: If a>0 and a*u+b*v=1, then gcd(a,b)=1.
  Proof: The gcd divides both inputs and hence their linear
  combination one. A divisor of one is at most one. The gcd is
  positive because a is nonzero, so it must equal one. QED
  -/
  rcases h with ⟨u,v,he⟩
  have hd := dvd_linear (gcd a b) a b u v
    (gcd_data a b).2.1 (gcd_data a b).2.2.1
  rw [he] at hd
  have hle := divisor_le_positive (gcd a b) 1 (by decide) hd
  have hpos := gcd_positive a b (Or.inl (by omega))
  omega


/- Each entry stores a prescribed remainder and its modulus. -/

def modulusProduct : List (Int × Int) → Int
  | [] => 1
  | entry :: rest => entry.2 * modulusProduct rest

theorem modulus_product_positive (system : List (Int × Int))
    (hpos : ∀ entry ∈ system, 0 < entry.2) : 0 < modulusProduct system := by
  /-
  Lemma: A finite product of positive moduli is positive.
  Proof: Induct on the list of congruences. The empty product is
  one. For a nonempty list, its first modulus and the product of
  the remaining moduli are positive, so their product is positive.
  QED
  -/
  induction system with
  | nil => exact (by decide : (0 : Int) < 1)
  | cons entry rest ih =>
    exact Int.mul_pos (hpos entry (List.mem_cons_self _ _))
      (ih (fun e he => hpos e (List.mem_cons_of_mem _ he)))

theorem bezout_modulus_product (n : Int) (system : List (Int × Int))
    (hcop : ∀ entry ∈ system, gcd n entry.2=1) :
    ∃ u v : Int, n*u+modulusProduct system*v=1 := by
  /-
  Lemma: If n is relatively prime to every modulus in a finite
  list, n and their product have a linear combination equal to one.
  Proof: Induct on the list. For the empty product one, use
  coefficients zero and one. For a nonempty list, Bezout supplies
  coefficients for n and the first modulus. The induction hypothesis
  supplies coefficients for n and the remaining product. Combining
  these two identities by the product lemma completes the step.
  QED
  -/
  induction system with
  | nil => exact ⟨0,1,by simp [modulusProduct]⟩
  | cons entry rest ih =>
    have hfirst := bezout n entry.2
    rw [hcop entry (List.mem_cons_self _ _)] at hfirst
    exact bezout_product n entry.2 (modulusProduct rest) hfirst
      (ih (fun e he => hcop e (List.mem_cons_of_mem _ he)))

def Satisfies (x : Int) (system : List (Int × Int)) : Prop :=
  ∀ entry ∈ system, Congruent x entry.1 entry.2

theorem finite_congruences (system : List (Int × Int))
    (hpos : ∀ entry ∈ system, 0 < entry.2)
    (hcop : system.Pairwise (fun e f => gcd e.2 f.2=1)) :
    ∃ r : Int, Satisfies r system ∧ ∀ x : Int,
      Satisfies x system ↔ Congruent x r (modulusProduct system) := by
  /-
  Theorem: A finite system with positive, pairwise relatively prime
  moduli has a solution, and all its solutions form exactly one
  congruence class modulo the product of its moduli.
  Proof: Induct on the number of congruences. The empty system
  accepts every integer, exactly the class of zero modulo one.
  For the induction step, the remaining congruences are equivalent
  to a single congruence modulo their product by the induction
  hypothesis. The first modulus is relatively prime to every
  remaining modulus, so the product Bezout lemma shows that it
  is relatively prime to their product too. Apply the two-modulus
  theorem to the first congruence and the combined remaining one.
  This gives precisely one class modulo the full product. Its
  representative satisfies the system, since its difference from
  itself is zero. Thus both existence and uniqueness follow. QED

  A list entry is (remainder, modulus). Pairwise compares distinct
  positions in this list. Including the empty list extends the
  statement harmlessly, using the empty product one.
  -/
  induction system with
  | nil =>
    refine ⟨0,?_,?_⟩
    · intro e he; cases he
    · intro x
      constructor
      · intro _
        exact ⟨by decide,x,by simp [modulusProduct]⟩
      · intro _ e he; cases he
  | cons entry rest ih =>
    have hp := List.pairwise_cons.mp hcop
    have hrest : ∀ e ∈ rest, 0 < e.2 :=
      fun e he => hpos e (List.mem_cons_of_mem _ he)
    rcases ih hrest hp.2 with ⟨r₀,_,hequiv⟩
    have hn := hpos entry (List.mem_cons_self _ _)
    have hprod := modulus_product_positive rest hrest
    have hrel := gcd_one_of_bezout entry.2 (modulusProduct rest) hn
      (bezout_modulus_product entry.2 rest hp.1)
    rcases two_coprime_congruences entry.1 r₀ entry.2
      (modulusProduct rest) hn hprod hrel with ⟨r,hr⟩
    have hall : ∀ x : Int, Satisfies x (entry::rest) ↔
        Congruent x r (modulusProduct (entry::rest)) := by
      intro x
      constructor
      · intro hx
        apply (hr x).mp
        exact ⟨hx entry (List.mem_cons_self _ _),
          (hequiv x).mp (fun e he => hx e (List.mem_cons_of_mem _ he))⟩
      · intro hx
        rcases (hr x).mpr hx with ⟨hfirst,htail⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · subst e; exact hfirst
        · exact (hequiv x).mpr htail e he
    refine ⟨r,(hall r).mpr ?_,hall⟩
    exact ⟨Int.mul_pos hn hprod,0,by simp⟩

end NumberTheory.SimultaneousCongruences
