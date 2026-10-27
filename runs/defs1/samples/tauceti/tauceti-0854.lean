public section

namespace TauCeti

open scoped Manifold ContDiff

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {I' : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace G M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

namespace SmoothEmbedding

variable {f g : SmoothEmbedding I J n M N}

/-- The inclusion of an open subset of a manifold as a bundled smooth embedding. -/
def ofOpens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    SmoothEmbedding I I n s M where
  toContMDiffMap :=
    ⟨Subtype.val, (Manifold.IsSmoothEmbedding.of_opens (I := I) (n := n) s).contMDiff⟩
  isSmoothEmbedding_toFun := Manifold.IsSmoothEmbedding.of_opens (I := I) (n := n) s

end SmoothEmbedding
end TauCeti
end
