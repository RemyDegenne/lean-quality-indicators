@[expose] public section

namespace KaltonPeck.Support.GraphFredholm

noncomputable
section

open Coordinates Symplectic

open HilbertGlidingHump

open StrictlySingular

open Filter Function

open scoped ENNReal NNReal Topology lp BigOperators InnerProductSpace

universe uX uY

universe u

theorem canonical_symplecticAdjoint_range_le_quotientKernel
    (R : CanonicalRealKaltonPeck →L[ℝ] CanonicalRealKaltonPeck)
    (hR : R.comp canonicalL2Inclusion = 0) :
    (canonicalKaltonSwansonForm.adjoint R).range ≤
      canonicalL2Quotient.ker := by
  rintro z ⟨x, rfl⟩
  change
    canonicalL2Quotient (canonicalKaltonSwansonForm.adjoint R x) = 0
  apply ext_inner_left ℝ
  intro y
  have hskew (a b : CanonicalRealKaltonPeck) :
      canonicalKaltonSwansonForm.toDual a b =
        -canonicalKaltonSwansonForm.toDual b a := by
    have h := canonicalKaltonSwansonForm.alternating (a + b)
    simp only [map_add, add_apply, canonicalKaltonSwansonForm.alternating,
      add_zero, zero_add] at h
    linarith
  calc
    inner ℝ y
        (canonicalL2Quotient
          (canonicalKaltonSwansonForm.adjoint R x)) =
        canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion y)
          (canonicalKaltonSwansonForm.adjoint R x) := by
      rw [Symplectic.canonicalKaltonSwansonForm_inclusion_left]
    _ = -canonicalKaltonSwansonForm.toDual
          (canonicalKaltonSwansonForm.adjoint R x)
          (canonicalL2Inclusion y) :=
      hskew _ _
    _ = -canonicalKaltonSwansonForm.toDual x
          (R (canonicalL2Inclusion y)) := by
      rw [Forms.adjoint_apply]
    _ = 0 := by
      have hy : R (canonicalL2Inclusion y) = 0 := by
        simpa only [ContinuousLinearMap.comp_apply, zero_apply] using
          DFunLike.congr_fun hR y
      rw [hy, map_zero, neg_zero]
    _ = inner ℝ y 0 := by simp

end
end KaltonPeck.Support.GraphFredholm
end
