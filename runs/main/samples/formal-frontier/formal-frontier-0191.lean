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

theorem stalkMap_isLocalHom (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) (x : M) :
    IsLocalHom ((locallyRingedSpaceMap IM IN M N r f hf).stalkMap x).hom :=
  (locallyRingedSpaceMap IM IN M N r f hf).prop x

end FiniteRegularityFunctions
end
end
