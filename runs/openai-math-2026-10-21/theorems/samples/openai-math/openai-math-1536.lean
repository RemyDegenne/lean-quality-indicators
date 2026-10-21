namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

open scoped NNReal ENNReal

theorem intrinsic_volume_le_of_lower_growth (n : ℕ) (C G : ℝ)
    (μ : Measure (Ambient n)) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x : Ambient n, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) :
    intrinsicLowerDensityBound n C • (volume : Measure (Ambient n)) ≤ μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  let V : ℝ := (volume : Measure (Ambient n)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne
  have hc : (intrinsicLowerDensityBound n C : ℝ) = (C * V)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.mpr (mul_nonneg hC.le hV.le))
  apply measure_le_of_closedBall_le
  intro x r hr
  have hvol : (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n * V := by
    simpa only [Ambient, finrank_euclideanSpace, Fintype.card_fin] using!
      (Measure.addHaar_real_closedBall (volume : Measure (Ambient n)) x hr.le)
  have hid : (intrinsicLowerDensityBound n C : ℝ) *
      (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n / C := by
    rw [hc, hvol]
    field_simp [hV.ne', hC.ne']
  calc
    (intrinsicLowerDensityBound n C • (volume : Measure (Ambient n))) (closedBall x r) =
        ENNReal.ofReal ((intrinsicLowerDensityBound n C : ℝ) *
          (volume : Measure (Ambient n)).real (closedBall x r)) := by
      rw [ENNReal.ofReal_mul (intrinsicLowerDensityBound n C).coe_nonneg,
        ENNReal.ofReal_coe_nnreal, Measure.real,
        ENNReal.ofReal_toReal (measure_closedBall_lt_top.ne), Measure.coe_nnreal_smul_apply]
    _ = ENNReal.ofReal (r ^ n / C) := congrArg ENNReal.ofReal hid
    _ ≤ μ (ball x r) := hlower x r hr
    _ ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall

end
end RieszRectifiability
end OAI
