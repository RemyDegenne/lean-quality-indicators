public section

namespace TauCeti

open Complex Metric Set

open scoped ComplexConjugate

lemma norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖z - w‖ < ‖1 - (starRingEnd ℂ) w * z‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  have hpos : 0 < (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact mul_pos (one_sub_sq_norm_pos_of_norm_lt_one hz)
      (one_sub_sq_norm_pos_of_norm_lt_one hw)
  have hdiff := normSq_one_sub_conj_mul_sub_normSq_sub z w
  nlinarith

end TauCeti
end
