public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal

open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

theorem mul_self_eq_one_of_mem_ker_spinAction_quadOdd (h2 : (2 : K) ≠ 0)
    {x : spinGroup (quadOdd n K)} (hx : x ∈ (spinAction (quadOdd n K)).ker) : x * x = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rcases (mem_ker_spinAction_iff _ (nondegenerate_quadOdd n K) x).mp hx with rfl | rfl
  · exact mul_one 1
  · exact spinGroup.negOne_mul_self _ _

end CFSG.ComponentClassification.HarrisLit.T1
end
