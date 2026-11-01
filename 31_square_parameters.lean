import «03_common_divisors»

namespace NumberTheory.SquareParameters

open NumberTheory.CommonDivisors

/-- Integer solutions of the Pell equation with natural parameter N. -/
def PellSolution (N : Nat) (x y : Int) : Prop :=
  x*x-(N:Int)*(y*y)=1

/-- The two solutions with first coordinate one or minus one and second coordinate zero. -/
def Trivial (x y : Int) : Prop :=
  (x=1 ∨ x = -1) ∧ y=0

theorem square_parameter_trivial (N : Nat) (hN : 0<N)
    (hsquare : ∃ k : Nat, N=k*k) (x y : Int)
    (h : PellSolution N x y) : Trivial x y := by
  /-
  Theorem: A positive square parameter has only trivial integer Pell
  solutions. Proof: Write N=k*k, with k>0, and factor the equation as
  (x-k*y)(x+k*y)=1. Put a=x-k*y and b=x+k*y. Since a divides one,
  a positive a is at most one. If a is negative, -a also divides one
  and is at most one. The case a=0 is impossible. Thus a=1 or a=-1;
  the product equation forces b to have the same value. Subtracting
  the factors gives 2*k*y=0, so y=0 because k>0. Adding them gives
  x=1 or x=-1, as required. QED

  The positivity hypothesis excludes N=0: in that case x=1 or x=-1
  solves the equation for every integer y, including nonzero y.
  -/
  obtain ⟨k,hk⟩ := hsquare
  have hkpos : 0<k := by
    by_cases hz : k=0
    · simp [hz] at hk
      omega
    · omega
  have hNI : (N:Int)=(k:Int)*(k:Int) := by
    rw [hk,Int.natCast_mul]
  let a := x-(k:Int)*y
  let b := x+(k:Int)*y
  have hab : a*b=1 := by
    have he := h
    dsimp [PellSolution] at he
    rw [hNI] at he
    dsimp [a,b]
    simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,
      Int.mul_assoc,Int.mul_comm,Int.mul_left_comm] at he ⊢
    omega
  have hane : a≠0 := by intro ha; rw [ha,Int.zero_mul] at hab; contradiction
  have hadvd : a∣1 := ⟨b,hab.symm⟩
  have ha : a=1 ∨ a = -1 := by
    by_cases hap : 0<a
    · have hle := divisor_le_positive a 1 (by decide) hadvd
      exact Or.inl (by omega)
    · have hneg : -a∣1 := ⟨-b,by simpa only [Int.neg_mul_neg] using hab.symm⟩
      have hle := divisor_le_positive (-a) 1 (by decide) hneg
      exact Or.inr (by omega)
  have hky : (k:Int)*y=0 := by
    rcases ha with ha|ha
    · rw [ha,Int.one_mul] at hab
      dsimp [a,b] at ha hab
      omega
    · rw [ha,Int.neg_mul,Int.one_mul] at hab
      dsimp [a,b] at ha hab
      omega
  have hy : y=0 := by
    have he : (k:Int)*y=(k:Int)*0 := by simpa using hky
    exact Int.eq_of_mul_eq_mul_left (by omega : (k:Int)≠0) he
  have hx : x=1 ∨ x = -1 := by simpa only [a,hy,Int.mul_zero,Int.sub_zero] using ha
  exact ⟨hx,hy⟩

end NumberTheory.SquareParameters
