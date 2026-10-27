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

/-- The locally ringed space associated with finite-`C^r` scalar functions. -/
@[implicit_reducible]
def locallyRingedSpace (r : ℕ) (IM : ModelWithCorners 𝕜 EM HM)
    (M : Type u) [TopologicalSpace M] [ChartedSpace HM M] : LocallyRingedSpace where
  carrier := ↧M
  presheaf := presheaf IM M r
  IsSheaf := (sheaf IM M r).property
  isLocalRing x := instLocalRingStalk (IM := IM) (M := M) r x

end FiniteRegularityFunctions
end
end
