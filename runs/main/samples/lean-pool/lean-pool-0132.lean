@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

section

@[expose] public section

namespace TauCeti

open Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_apply_lt_and_lt_norm {φ : E →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u R : ℝ) :
    ∃ y : E, φ y < u ∧ R < ‖y‖ := by
  obtain ⟨v, hφv⟩ := LinearMap.surjective_iff_ne_zero.mpr hφ 1
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr fun h => by simp [h] at hφv
  -- Walk to `-t • v` for a `t` large enough to break both the bound `u` and the radius `R`.
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, (R + 1) / ‖v‖ ≤ t ∧ |u| + 1 ≤ t :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have ht0 : 0 ≤ t := le_trans (by positivity) ht2
  refine ⟨(-t) • v, ?_, ?_⟩
  · rw [map_smul, hφv, smul_eq_mul, mul_one]
    linarith [neg_abs_le u]
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith [(div_le_iff₀ hvnorm).mp ht1]

end TauCeti
end
end
end
end
end
end
end
end
