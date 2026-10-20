public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

open scoped NNReal

variable {γ : ℝ → ℂ} {a b : ℝ}

theorem IsPwC1ImmersionOn.exists_Icc_piece_left (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioc (min a b) (max a b)) :
    ∃ c : ℝ, c < t₀ ∧ Icc c t₀ ⊆ uIcc a b ∧ ContDiffOn ℝ 1 γ (Icc c t₀) ∧
      ∀ t ∈ Icc c t₀, derivWithin γ (Icc c t₀) t ≠ 0 := by
  obtain ⟨p, hp, hpieces⟩ := h.exists_breakpoints
  obtain ⟨c, hlt, hsub, hdisj⟩ := exists_Icc_left_avoiding hp ht₀
  exact ⟨c, hlt, hsub, hpieces c t₀ hlt hsub hdisj⟩

end TauCeti.Contour
end
end
