@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped ContDiff Manifold

universe u v w

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type w} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)
  {M : Type u} [TopologicalSpace M]

/-- The canonical smooth scalar locally ringed space for a specified atlas. -/
def smoothScalarLocallyRingedSpace (C : ChartedSpace H M) : LocallyRingedSpace := by
  letI : ChartedSpace H M := C
  exact locallyRingedSpace I M

end ChartedSpace
end
end
