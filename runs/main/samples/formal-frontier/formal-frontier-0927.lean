@[expose] public section

open CategoryTheory Function

namespace Profinite.FinitePresentation

universe u

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

theorem injectiveStageMap_injective (B : DiscreteQuotient Y) :
    Injective (injectiveStageMap f B) := by
  rintro ⟨x⟩ ⟨y⟩ h
  change B.proj (f x) = B.proj (f y) at h
  apply Quotient.sound
  change B.toSetoid (f x) (f y)
  exact Quotient.exact h

end Profinite.FinitePresentation
end
