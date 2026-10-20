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

@[simp] theorem smoothScalarLocallyRingedSpace_carrier (C : ChartedSpace H M) :
    (smoothScalarLocallyRingedSpace I C).carrier = ↧M := rfl

end ChartedSpace
end
end
