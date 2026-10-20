@[expose] public section

open ENNReal Set SignType

noncomputable section

namespace EReal

open SignType (sign)

lemma sign_mul_inv_abs' (a : EReal) : (sign a) * ((a.abs⁻¹ : ℝ≥0∞) : EReal) = a⁻¹ := by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_neg a_neg), coe_ennreal_ofReal,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_pos a_pos), coe_ennreal_ofReal,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos

end EReal
end
end
