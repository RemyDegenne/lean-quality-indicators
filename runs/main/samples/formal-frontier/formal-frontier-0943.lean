@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u

namespace ChartedSpace.ChartLocalBall

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {x : M} (b : ChartLocalBall (𝕜 := 𝕜) (E := E) (∞ : ℕ∞ω) x)

@[simp] theorem restrict_smoothIso_hom_base (point : b.neighborhood) :
    ((restrictLocallyRingedSpaceIso (IM := 𝓘(𝕜, E)) (M := M)
      b.neighborhood).inv ≫ b.smoothIso.hom).base point = b.coord point := by
  rw [b.restrict_smoothIso_hom]
  rfl

end ChartedSpace.ChartLocalBall
end
end
