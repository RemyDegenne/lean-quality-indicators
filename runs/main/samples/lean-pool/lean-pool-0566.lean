@[expose] public section

section

open MeasureTheory Set Filter

open scoped ENNReal Topology BigOperators

open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Heat

open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

theorem fixed_pressure_cylinder_subset_ball
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R) :
    parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R ⊆ Metric.ball z₀ R := by
  rw [metricBall_eq_parabolicBall]
  intro z hz
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  exact ⟨hz.1, by nlinarith only [hz.2.1, hs], by nlinarith only [hz.2.2, hs]⟩

end CKN.Core.Step4
end
end
end
