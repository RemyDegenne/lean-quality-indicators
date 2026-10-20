public section

noncomputable section

open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace ContractionSemigroup

theorem orbit_ball (S : ContractionSemigroup X) (t :
    ℝ≥0) {x : X} {r : ℝ} (hx : x ∈ Metric.ball 0 r) :
    S t x ∈ Metric.ball 0 r := by
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hx ⊢
  exact (S.norm_apply_le t x).trans_lt hx

end ContractionSemigroup
end TauCeti.Semigroups
end
end
