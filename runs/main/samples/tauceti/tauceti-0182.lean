public section

open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable {E H M E' H' M' E'' H'' M'' : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M''] [ChartedSpace H'' M'']
  [IsManifold I'' ∞ M'']

variable {j : SmoothAlmostComplexStructure I M} {J : SmoothAlmostComplexStructure I' M'}
  {K : SmoothAlmostComplexStructure I'' M''} {u : M → M'} {v : M' → M''} {s t : Set M}
  {x : M}

theorem IsPseudoholomorphic.comp (hv : IsPseudoholomorphic J K v)
    (hu : IsPseudoholomorphic j J u) : IsPseudoholomorphic j K (v ∘ u) :=
  fun x ↦ (hv (u x)).comp (hu x)

end TauCeti
end
end
