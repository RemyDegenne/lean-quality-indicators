public section

open Bundle InnerProductSpace Laplacian Module TauCeti.Manifold

open scoped ContDiff Manifold Gradient

noncomputable section

namespace TauCeti.Yamabe

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

theorem conformalLaplacian_add {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (x : M) :
    conformalLaplacian I (u + v) x = conformalLaplacian I u x + conformalLaplacian I v x := by
  simp only [conformalLaplacian_def, laplaceBeltrami_add I hu hv x, Pi.add_apply]
  ring

end Manifold
end TauCeti.Yamabe
end
end
