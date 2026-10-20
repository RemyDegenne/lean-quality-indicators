public section

noncomputable section

namespace TauCeti

open Set Filter Manifold Topology

open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

namespace Concordance

variable {f g h : SmoothEmbedding I J n M N}

variable (F : Concordance f g)

variable [IsManifold I n M] [IsManifold J n N]

/-- The constant concordance from `f` to itself, whose track is `f × id`. -/
def refl (f : SmoothEmbedding I J n M N) : Concordance f f where
  toSmoothEmbedding := f.prodMap SmoothEmbedding.id
  isCollaredTrack_toSmoothEmbedding := by
    rw [coe_prodMap, coe_id]
    exact isCollaredTrack_prodMap_id f

end Concordance
end SmoothEmbedding
end TauCeti
end
end
