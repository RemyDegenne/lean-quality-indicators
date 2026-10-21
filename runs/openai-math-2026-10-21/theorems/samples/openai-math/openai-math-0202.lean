namespace OAI

namespace PiExponent

theorem exists_weight_error_margin
    (m : ℕ) (Λ S ε : ℝ) (_hΛ : 0 < Λ) (_hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ wstar : ℝ, X < wstar →
      Λ * (m : ℝ) / wstar + S / wstar < ε := by
  refine ⟨max 1 ((Λ * (m : ℝ) + S) / ε), le_max_left _ _, ?_⟩
  intro wstar hwstar
  have hwpos : 0 < wstar :=
    lt_of_lt_of_le zero_lt_one (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hwstar))
  have hquot : (Λ * (m : ℝ) + S) / ε < wstar :=
    lt_of_le_of_lt (le_max_right _ _) hwstar
  have hnum : Λ * (m : ℝ) + S < ε * wstar := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hquot
  rw [← add_div]
  exact (div_lt_iff₀ hwpos).mpr hnum

end PiExponent
end OAI
