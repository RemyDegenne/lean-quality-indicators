public section

namespace TauCeti

universe u v w

section Semiprimary

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

theorem IsProjectiveCover.exists_isMinimalProjectivePresentation [IsSemiprimaryRing R]
    {P₀ : Type w} [AddCommGroup P₀] [Module R P₀] {p₀ : P₀ →ₗ[R] M}
    (h₀ : IsProjectiveCover p₀) :
    ∃ (P₁ : Type max u w) (_ : AddCommGroup P₁) (_ : Module R P₁) (p₁ : P₁ →ₗ[R] P₀),
      IsMinimalProjectivePresentation p₁ p₀ := by
  obtain ⟨P₁, h₁⟩ := exists_isProjectiveCover R ↥(LinearMap.ker p₀)
  exact ⟨↥P₁, inferInstance, inferInstance,
    (LinearMap.ker p₀).subtype ∘ₗ (Finsupp.linearCombination R id ∘ₗ P₁.subtype),
    h₀.isMinimalProjectivePresentation h₁⟩

end Semiprimary
end TauCeti
end
