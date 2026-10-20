@[expose] public section

open Module

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField.InfinitePlace Module Finset

noncomputable section stdBasis

open Complex MeasureTheory MeasureTheory.Measure ZSpan Matrix

open scoped ComplexConjugate

variable [NumberField K]

variable {K}

variable (K)

variable {K}

variable (K)

open scoped Classical in
theorem det_matrixToStdBasis :
    (matrixToStdBasis K).det = (2⁻¹ * I) ^ nrComplexPlaces K :=
  calc
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, det ((2 : ℂ)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrixToStdBasis, det_fromBlocks_zero₂₁, det_diagonal, prod_const_one, one_mul,
          det_reindex_self, det_blockDiagonal]
  _ = ∏ _k : { w : InfinitePlace K // IsComplex w }, (2⁻¹ * Complex.I) := by
      refine prod_congr (Eq.refl _) (fun _ _ => ?_)
      simp [field]; ring
  _ = (2⁻¹ * Complex.I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} := by
      rw [prod_const, Fintype.card]

end stdBasis
end NumberField.mixedEmbedding
end
