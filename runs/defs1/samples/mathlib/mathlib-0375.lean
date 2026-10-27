@[expose] public section

namespace CategoryTheory

open Localization Category CategoryTheory.Functor

namespace Adjunction

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)

section

variable (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)
  [CatCommSq G L₁ L₂ G'] [CatCommSq F L₂ L₁ F']

namespace Localization

/-- Auxiliary definition of the counit morphism for the adjunction `Adjunction.localization` -/
noncomputable def η : F' ⋙ G' ⟶ 𝟭 D₂ := by
  letI : Lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    Lifting.mk (CatCommSq.hComp F G L₂ L₁ L₂ F' G').iso.symm
  exact liftNatTrans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂) (whiskerRight adj.counit L₂)

end Localization
end
end Adjunction
end CategoryTheory
end
