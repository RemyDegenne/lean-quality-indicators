namespace OAI

noncomputable section

open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory

open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped Manifold

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem exists_tangent_derivative (f : RegularHomogeneous W)
    (u : Metric.sphere (0 : W) 1) (hu : f u = 0) :
    ∃ v : W, ⟪(u : W), v⟫_ℝ = 0 ∧ fderiv ℝ f u v ≠ 0 := by
  have hne := f.regular (u : W) (unit_ne_zero u)
  have hv : ∃ v : W, fderiv ℝ f u v ≠ 0 := by
    by_contra! hall
    apply hne
    ext v
    exact hall v
  obtain ⟨v, hv⟩ := hv
  refine ⟨v - ⟪(u : W), v⟫_ℝ • (u : W), ?_, ?_⟩
  · rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    simp
  · simpa only [map_sub, map_smul, f.euler, hu, mul_zero, smul_zero, sub_zero] using hv

end NearbyLagrangian.Tubes.RegularHomogeneous
end
end OAI
