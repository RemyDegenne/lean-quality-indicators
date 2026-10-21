namespace OAI

namespace JointDickman

open scoped BigOperators

theorem finiteResidueAverage_sum {S R : Type*} [Fintype S] [Fintype R] (f : S → R → ℝ) :
    finiteResidueAverage (fun r => ∑ s, f s r) = ∑ s, finiteResidueAverage (f s) := by
  unfold finiteResidueAverage
  rw [Finset.sum_comm, Finset.sum_div]

end JointDickman
end OAI
