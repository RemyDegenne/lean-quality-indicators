public section

namespace TauCeti.Hodge.StandardWeightOne

open IsBaseChange

open Matrix

open scoped TensorProduct

variable (l : Type*)

noncomputable local instance moduleRatOfComplex : Module ℚ (ComplexSpace l) :=
  Module.restrictScalars ℚ ℂ (ComplexSpace l)

variable [Fintype l] [DecidableEq l]

theorem isRiemannForm_riemannForm :
    (almostComplexStructure l).IsRiemannForm (riemannForm l) where
  isAlt x := by
    simp only [riemannForm_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by ring
  invariant x y := by
    rw [baseChange_riemannForm_apply, baseChange_riemannForm_apply,
      realCoord_almostComplexStructure, realCoord_almostComplexStructure, ← toLin'_apply,
      ← toLin'_apply, ← LinearMap.BilinForm.comp_apply, toBilin'_comp, J_transpose, Matrix.neg_mul,
      J_squared, neg_neg, Matrix.one_mul]
  positive x hx := by
    -- `E_ℝ (J x) x = (J x) ⬝ᵥ (J x)`, a sum of squares, and `J x ≠ 0` since `J` is invertible.
    rw [baseChange_riemannForm_apply, realCoord_almostComplexStructure, toBilin'_apply']
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _) (Ne.symm ?_)
    rw [Ne, dotProduct_self_eq_zero]
    intro h
    have h' := congrArg (J l ℝ *ᵥ ·) h
    simp only [mulVec_mulVec, J_squared, mulVec_zero, neg_mulVec, one_mulVec, neg_eq_zero,
      LinearEquiv.map_eq_zero_iff] at h'
    exact hx h'

end TauCeti.Hodge.StandardWeightOne
end
