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

section Sections

variable {IM M}

@[simp] theorem sectionRingEquiv_apply (r : ℕ) (U : Opens M)
    (f : (sheaf IM M r).presheaf.obj (op U)) (point : U) :
    sectionRingEquiv (IM := IM) (M := M) r U f point = f point := by
  rfl

end Sections
end FiniteRegularityFunctions
end
end
