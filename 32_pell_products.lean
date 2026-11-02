import «31_square_parameters»

namespace NumberTheory.PellProducts

open NumberTheory.SquareParameters

theorem multiply_solutions (N : Nat) (a b c d : Int)
    (hab : PellSolution N a b) (hcd : PellSolution N c d) :
    PellSolution N (a*c+(N:Int)*b*d) (a*d+b*c) := by
  /-
  Theorem: If (a,b) and (c,d) are integer Pell solutions for the same
  natural parameter N, then (a*c+N*b*d,a*d+b*c) is also a solution.
  Proof: The two given equations each have right-hand side one, so
  their product is one. Expand the proposed equation's left-hand side:

    (a*c+N*b*d)^2-N*(a*d+b*c)^2
      = a^2*c^2+2*N*a*b*c*d+N^2*b^2*d^2
        -N*a^2*d^2-2*N*a*b*c*d-N*b^2*c^2
      = (a^2-N*b^2)*(c^2-N*d^2)
      = 1*1 = 1.

  The mixed terms cancel, and the remaining terms are exactly the
  product of the given equations. The new coordinates are integers
  because they are sums and products of integers. QED

  No positivity or nonsquare restriction on N is needed for this
  identity, and the coordinates may have either sign or be zero.
  -/
  have hproduct : (a*a-(N:Int)*(b*b))*(c*c-(N:Int)*(d*d))=1 := by
    rw [hab,hcd,Int.one_mul]
  have hidentity :
      (a*c+(N:Int)*b*d)*(a*c+(N:Int)*b*d)-
        (N:Int)*((a*d+b*c)*(a*d+b*c)) =
      (a*a-(N:Int)*(b*b))*(c*c-(N:Int)*(d*d)) := by
    simp only [Int.mul_add,Int.add_mul,Int.mul_sub,Int.sub_mul,
      Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    omega
  exact hidentity.trans hproduct

end NumberTheory.PellProducts
