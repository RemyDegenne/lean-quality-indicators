namespace OAI

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory Filter Set

open scoped Topology ENNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem coe_finiteMetricNeighborhood
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) {R : ℝ} (hR : 0 ≤ R) :
    (↑(finiteMetricNeighborhood hfinite E R) : Set G) = cthickening R (E : Set G) := by
  rw [E.finite_toSet.isCompact.cthickening_eq_biUnion_closedBall hR]
  ext x
  simp only [Finset.mem_coe, mem_finiteMetricNeighborhood, Set.mem_iUnion, mem_closedBall,
    exists_prop]

end PolycyclicRecognition
end
end OAI
