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

end NumberTheory.SquarePairs
