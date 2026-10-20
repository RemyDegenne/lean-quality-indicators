@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u v w x y z

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type v} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type w} [TopologicalSpace HM]
  (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type z} [TopologicalSpace M] [ChartedSpace HM M]

variable {IM} {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  {EN : Type x} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type y} [TopologicalSpace HN]
  {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]
  (IN : ModelWithCorners 𝕜 EN HN)

theorem preservesSmoothScalars_id :
    PreservesSmoothScalars (M := M) (N := M) IM
      (𝟙 (locallyRingedSpace IM M).toPresheafedSpace) := by
  intro a point
  rfl

end ChartedSpace
end
end
