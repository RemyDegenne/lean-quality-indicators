public section

noncomputable section

open Set Function Topology Bundle Metric

open scoped Manifold ContMDiff Set.Notation

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

@[simp]
theorem normalBundleHomeomorphTubeOfRadius_apply_snd (f : M → V) (r : C(M, ℝ))
    (hr : ∀ x, 0 < r x) (p : TotalSpace V (fun x : M => normalSubspace I f x)) :
    (normalBundleHomeomorphTubeOfRadius f r hr p).1.2 =
      r p.proj • (Real.sqrt (1 + ‖(p.2 : V)‖ ^ 2))⁻¹ • (p.2 : V) := by
  simp [normalBundleHomeomorphTubeOfRadius, Homeomorph.unitBall_apply_coe,
    OpenPartialHomeomorph.univUnitBall_apply]

end TauCeti
end
end
