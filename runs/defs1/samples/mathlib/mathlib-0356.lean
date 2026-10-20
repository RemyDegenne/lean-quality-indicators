@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₅] [Category* C₆]

variable (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace CatCommSq

/-- A variant of `vComp` where both squares can be explicitly provided. -/
abbrev vComp' {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {H₁ : C₁ ⥤ C₄} {H₂ : C₂ ⥤ C₅} {H₃ : C₃ ⥤ C₆}
    {R₁ : C₄ ⥤ C₅} {R₂ : C₅ ⥤ C₆} (S₁ : CatCommSq H₁ L₁ R₁ H₂) (S₂ : CatCommSq H₂ L₂ R₂ H₃) :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ :=
  letI := S₁
  letI := S₂
  vComp _ _ _ H₂ _ _ _

end CatCommSq
end CategoryTheory
end
