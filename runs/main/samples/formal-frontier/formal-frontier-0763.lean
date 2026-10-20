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

theorem precompose_restrict (r : ℕ) (f : M → N)
    (hf : ContMDiff IM IN (r : ℕ∞ω) f) {U V : Opens N} (h : U ≤ V)
    (s : (sheaf IN N r).presheaf.obj (op V)) :
    precompose IM IN M N r f hf U (restrict (IM := IN) (M := N) r h s) =
      restrict (IM := IM) (M := M) r
        (show ContinuousFunctions.inverseImage M N f hf.continuous U ≤
          ContinuousFunctions.inverseImage M N f hf.continuous V from
            fun _ hx => h hx)
        (precompose IM IN M N r f hf V s) := by
  apply section_ext (IM := IM) (M := M)
  intro point
  rfl

end FiniteRegularityFunctions
end
end
