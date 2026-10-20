public section

noncomputable section

namespace TauCeti

open Manifold Set

open scoped Manifold ContDiff

namespace SmoothEmbedding

section Bundled

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω}

@[simp]
theorem compDiffeomorph_compDiffeomorph [IsManifold I n M']
    [IsManifold I n M''] (f : SmoothEmbedding I J n M N) (e : M' ≃ₘ^n⟮I, I⟯ M)
    (e' : M'' ≃ₘ^n⟮I, I⟯ M') :
    (f.compDiffeomorph e).compDiffeomorph e' = f.compDiffeomorph (e'.trans e) := by
  apply SmoothEmbedding.ext
  intro x
  rw [compDiffeomorph_apply, compDiffeomorph_apply, compDiffeomorph_apply]
  rfl

end Bundled
end SmoothEmbedding
end TauCeti
end
end
