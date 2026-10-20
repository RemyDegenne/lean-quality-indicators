@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u

namespace FiniteRegularityFunctions

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] (IN : ModelWithCorners 𝕜 EN HN)
  (M N : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  [TopologicalSpace N] [ChartedSpace HN N]

@[simp] theorem precompose_apply (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (U : Opens N)
    (s : (sheaf IN N r).presheaf.obj (op U))
    (point : ContinuousFunctions.inverseImage M N f hf.continuous U) :
    precompose IM IN M N r f hf U s point = s ⟨f point.1, point.2⟩ := by
  rfl

end FiniteRegularityFunctions
end
end
