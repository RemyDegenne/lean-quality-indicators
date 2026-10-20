@[expose] public section

open Bundle Bornology

open scoped ComplexConjugate

namespace Bundle

/-- The standard continuous metric on a trivial bundle with an inner-product model.
This constructor uses the given inner product, independently of the finite-dimensional existence
construction, and needs neither finite dimension nor separation assumptions on the base. -/
noncomputable def ContinuousHermitianMetric.trivial (𝕜 : Type*) [RCLike 𝕜]
    (B : Type*) [TopologicalSpace B] (V : Type*) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] :
    ContinuousHermitianMetric 𝕜 V (Bundle.Trivial B V) where
  inner _ := innerSL 𝕜
  symm _ v w := inner_conj_symm v w
  pos _ v hv := by
    rw [innerSL_apply_apply, inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  isVonNBounded _ := by
    apply NormedSpace.isVonNBounded_of_isBounded 𝕜
    apply Metric.isBounded_ball.subset (t := Metric.ball (0 : V) 1)
    intro v hv
    simp only [Set.mem_ofPred_eq, innerSL_apply_apply, inner_self_eq_norm_sq] at hv
    simpa only [Metric.mem_ball, dist_zero_right, abs_norm] using
      (sq_lt_one_iff_abs_lt_one ‖v‖).mp hv
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_id, ?_⟩
    convert! continuousAt_const (y := innerSL 𝕜 (E := V))
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]

end Bundle
end
