section

section

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerSmoothSobolev Finset

open scoped ContDiff Topology

theorem regularized_rhs_error (n : ℕ) (A : SmoothL2Field Space)
    (hA : A.toLp ∈ solenoidalSpace) (M : ℝ) (hM : WordBound 4 M A) :
    ‖((regularizer n).rhs A.toLp).toLp-(projectedRhs A).toLp‖ ≤
      regularizerError n*regularizationCost M := by
  let S := regularizer n
  let B := S.field A.toLp
  have hB : WordBound 4 M B := S.field_wordBound A 4 M hM
  have he := regularizer_error_words n A hA 1 M (wordBound_mono hM (by omega))
  have he0 : ‖B.toLp-A.toLp‖ ≤ regularizerError n*M := by
    simpa only [toLp_fieldSub] using wordBound_toLp he
  have he1 : ‖B.jetLp 1-A.jetLp 1‖ ≤ 3*(regularizerError n*M) := by
    simpa only [jetLp_fieldSub,pow_one] using wordBound_jet_norm he (le_refl 1)
  have hadv : ‖(advectionField B B).toLp-(advectionField A A).toLp‖ ≤
      ((360*smoothEmbeddingConstant)*M)*(regularizerError n*M) +
      ((13*smoothEmbeddingConstant)*M)*(3*(regularizerError n*M)) := by
    apply (advection_sub_norm B A _ _ (wordBound_gradient (wordBound_mono hB (by omega)))
      (wordBound_pointwise (wordBound_mono hM (by omega)))).trans
    exact add_le_add (mul_le_mul_of_nonneg_left he0
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
      (mul_le_mul_of_nonneg_left he1
      (mul_nonneg (mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg) (wordBound_nonneg hM)))
  have hp := regularizer_error_wordBound n (advectionField B B) _ (advection_low_words B M hB)
  have hq : ‖solenoidalProjection (advectionField B B).toLp -
      solenoidalProjection (advectionField A A).toLp‖ ≤
      ‖(advectionField B B).toLp-(advectionField A A).toLp‖ := by
    rw [← map_sub]
    exact solenoidalProjection_apply_norm_le _
  have heq : ((regularizer n).rhs A.toLp).toLp-(projectedRhs A).toLp =
      -(S.op (advectionField B B).toLp-solenoidalProjection (advectionField A A).toLp) := by
    simp only [SmoothingOperator.rhs_toLp,SmoothingOperator.quadratic_apply,projectedRhs_toLp,S,B]
    abel
  rw [heq,norm_neg]
  apply (norm_sub_le_norm_sub_add_norm_sub (S.op (advectionField B B).toLp)
    (solenoidalProjection (advectionField B B).toLp)
    (solenoidalProjection (advectionField A A).toLp)).trans
  exact (add_le_add hp (hq.trans hadv)).trans_eq (by unfold regularizationCost; ring)

end EulerOrdinarySobolev
end
end
end
end
