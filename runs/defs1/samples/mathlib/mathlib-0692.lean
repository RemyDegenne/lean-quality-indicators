@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Limits

open Opposite

variable {C : Type u₁} [Category.{u₂} C] {I : Type v₁} [Category.{v₂} I]

section IndYonedaContravariant

variable (D : I ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Type u₂)

variable [HasColimit (D.leftOp ⋙ yoneda)] [HasLimitsOfShape I (Type (max u₁ u₂))]

/-- Ind-Yoneda lemma: morphisms from colimit of yoneda of diagram `D` to `F` is limit of `F`
evaluated at `D`. This version is for contravariant diagrams, see `colimitYonedaHomIsoLimit` for a
covariant version. -/
noncomputable def colimitYonedaHomIsoLimit' :
    (colimit (D.leftOp ⋙ yoneda) ⟶ F) ≅ limit (D ⋙ F ⋙ uliftFunctor.{u₁}) :=
  colimitHomIsoLimitYoneda' _ F ≪≫
    HasLimit.isoOfNatIso (Functor.isoWhiskerLeft (D ⋙ Prod.sectL _ _) (yonedaLemma C))

end IndYonedaContravariant
end Limits
end CategoryTheory
end
