namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

section EndpointDifference

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalEndpointRule

variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

variable (o : V) (q : LocalEndpointRule G hloc (vertexOrbit G o) M L)

theorem differenceRow_finite (p r : unitInterval) :
    q.differenceRow o p r = ∑ y ∈ (finite_reachBall hloc o M).toFinset, q.kernelDifference o p r o y := by
  apply tsum_eq_sum
  intro y hy
  exact q.kernelDifference_outside o p r o y (by simpa only [Set.Finite.mem_toFinset] using hy)

end LocalEndpointRule
end EndpointDifference
end Percolation
end OAI
