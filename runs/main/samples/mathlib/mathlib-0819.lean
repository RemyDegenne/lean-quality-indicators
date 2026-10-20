@[expose] public section

open Filter Metric Set

open scoped ComplexConjugate Real Topology

namespace Complex

variable {a x z : ℂ}

theorem neg_pi_div_two_le_arg_iff {z : ℂ} : -(π / 2) ≤ arg z ↔ 0 ≤ re z ∨ 0 ≤ im z := by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him]
    rw [iff_true, arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.neg_pi_div_two_le_arcsin _).trans (le_add_of_nonneg_right Real.pi_pos.le)
  · simp only [him.not_ge]
    rw [iff_false, not_le, arg_of_re_neg_of_im_neg hre him, sub_lt_iff_lt_add', ←
      sub_eq_add_neg, sub_half, Real.arcsin_lt_pi_div_two, div_lt_one, neg_im, ← abs_of_neg him,
      abs_im_lt_norm]
    exacts [hre.ne, norm_pos_iff.mpr <| ne_of_apply_ne re hre.ne]

end Complex
end
