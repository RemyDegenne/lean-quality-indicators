public section

noncomputable section

open Set

open scoped ContDiff Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X)

omit [CompleteSpace X] in
theorem IsSmoothVector.realOperator {x : X} (hx : S.IsSmoothVector x) {t : ℝ}
    (ht : 0 ≤ t) : S.IsSmoothVector (S.realOperator t x) :=
  fun n => S.realOperator_mem_domainPow ht (hx n)

end StronglyContinuousSemigroup
end TauCeti.Semigroups
end
end
