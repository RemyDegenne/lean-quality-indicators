public section

noncomputable section

namespace TauCeti

open Set

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace UnorientedSmoothCircleEmbedding

/-- The embedded circle underlying an unoriented presentation. -/
def range (u : UnorientedSmoothCircleEmbedding I M) : Set M :=
  Quotient.lift (fun f : SmoothCircleEmbedding I M => Set.range f)
    (by
      intro f g h
      rcases (SmoothCircleEmbedding.unorientedSetoid_apply f g).mp h with rfl | h
      · rfl
      · rw [h, SmoothCircleEmbedding.range_reverse]) u

end UnorientedSmoothCircleEmbedding
end TauCeti
end
end
