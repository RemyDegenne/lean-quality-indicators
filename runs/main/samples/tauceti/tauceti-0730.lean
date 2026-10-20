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

section StandardLine

theorem IsPseudoholomorphicAt.mfderiv_stdComplexLineImag {J : SmoothAlmostComplexStructure I' M'}
    {w : ℝ × ℝ → M'} {z : ℝ × ℝ}
    (hw : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.product ℝ) J w z) :
    mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I' w z stdComplexLineImag =
      J (w z) (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I' w z stdComplexLineReal) := by
  have hz : SmoothAlmostComplexStructure.product ℝ z stdComplexLineReal = stdComplexLineImag := by
    simp only [SmoothAlmostComplexStructure.product_apply, stdComplexLineReal_fst,
      stdComplexLineReal_snd, neg_zero, stdComplexLineImag]
    rfl
  simpa only [hz] using hw.mfderiv_apply_commute stdComplexLineReal

end StandardLine
end TauCeti
end
end
