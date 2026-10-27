@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₅] [Category* C₆]

variable (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace CatCommSq

/-- Vertical composition of 2-commutative squares -/
@[simps!, instance_reducible]
def vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃] :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  iso := (associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (associator _ _ _).symm

end CatCommSq
end CategoryTheory
end
