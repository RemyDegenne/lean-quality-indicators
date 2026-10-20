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

/-- At order zero, continuity of a scalar function gives a finite-order section. -/
def continuousToZero (U : Opens M) :
    (ContinuousFunctions.sheaf M 𝕜).presheaf.obj (op U) →+*
      (sheaf IM M 0).presheaf.obj (op U) where
  toFun representative :=
    ⟨representative, contMDiff_zero_iff.mpr representative.hom.continuous⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' := by intros; apply Subtype.ext; rfl
  map_zero' := by apply Subtype.ext; rfl
  map_add' := by intros; apply Subtype.ext; rfl

end Comparisons
end FiniteRegularityFunctions
end
end
