@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite

open scoped ContDiff Manifold

universe u

namespace FiniteRegularityFunctions

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

variable {IM M}

section Comparisons

theorem smoothToFinite_app (r : ℕ) (U : Opens M) :
    (smoothToFinite (IM := IM) (M := M) r).hom.app (op U) =
      CommRingCat.ofHom (smoothToFiniteSection (IM := IM) (M := M) r U) := by
  rfl

end Comparisons
end FiniteRegularityFunctions
end
end
