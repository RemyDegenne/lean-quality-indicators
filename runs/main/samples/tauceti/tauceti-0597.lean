public section

open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {n : ℕ∞ω}

@[simp]
theorem toContMDiffMap_trans (f : M ≃ₘ^n⟮I, J⟯ N) (g : N ≃ₘ^n⟮J, I'⟯ P) :
    (f.trans g).toContMDiffMap = g.toContMDiffMap.comp f.toContMDiffMap := (rfl)

end Diffeomorph
end
