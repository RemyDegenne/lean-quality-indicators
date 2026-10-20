public section

namespace TauCeti.Toric

@[simp]
theorem mem_projectiveLineFan_cones (σ : PointedCone ℝ (Fin 1 → ℝ)) :
    σ ∈ projectiveLineFan.cones ↔
      σ = ⊥ ∨ σ = affineRayCone ∨ σ = negativeRayCone := by
  simp only [projectiveLineFan, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · rw [affineRayCone_def] at h
      rcases h.eq_bot_or_eq_of_hull_singleton 1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (h.trans affineRayCone_def.symm))
    · rw [negativeRayCone_def] at h
      rcases h.eq_bot_or_eq_of_hull_singleton (-(1 : Fin 1 → ℝ)) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (h.trans negativeRayCone_def.symm))
  · rintro (h | h | h)
    · subst σ
      exact Or.inl isRegularCone_affineRayCone.toIsToricCone.salient.bot_isFaceOf
    · subst σ
      exact Or.inl (PointedCone.IsFaceOf.refl _)
    · subst σ
      exact Or.inr (PointedCone.IsFaceOf.refl _)

end TauCeti.Toric
end
