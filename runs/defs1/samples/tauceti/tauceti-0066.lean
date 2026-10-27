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

/-- The stacked concordance from `f` to `h`: the concordance `F` from `f` to `g` at triple speed
during `[0, 1/3]`, then the constant concordance at `g`, then the concordance `G` from `g` to `h`
at triple speed during `[2/3, 1]`. -/
def trans [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h) :
    Concordance f h where
  toSmoothEmbedding := .ofIsSmoothEmbedding (stack F G) (isSmoothEmbedding_stack F G)
  isCollaredTrack_toSmoothEmbedding := by
    rw [coe_ofIsSmoothEmbedding]
    exact F.isCollaredTrack.stack G.isCollaredTrack

end Concordance
end SmoothEmbedding
end TauCeti
end
end
