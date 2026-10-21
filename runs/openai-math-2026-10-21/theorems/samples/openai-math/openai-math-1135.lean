namespace OAI

section

section

open Set MeasureTheory ProbabilityTheory

open Real

open Set Real

open scoped Topology

open scoped BigOperators

open Set

open Set MeasureTheory

open scoped Classical

open Set MeasureTheory Real

open scoped Interval

namespace CriticalPercolation.Priority

variable {I : Type*} [Fintype I]

open FiniteEntropy in

lemma weighted_fresh_identity (i : I) (S : Finset {j : I // j ≠ i}) (hS : S.card ≤ 3) :
    (∫ u in freshSet i S, endpointKernel (u i) ∂law) = 1 := by
  rw [integral_freshSet _ continuous_endpointKernel, uniform01_integral_eq_interval]
  exact integral_endpointKernel_power hS

end CriticalPercolation.Priority
end
end
end OAI
