@[expose] public section

namespace CategoryTheory.Lax

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {F G H I : B ⥤ᴸ C}

namespace OplaxTrans

set_option backward.defeqAttrib.useBackward true in
/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ (F.map f ◁ Γ.as.app b ≫ θ.naturality f) ▷ ι.app b ⊗≫
              θ.app a ◁ ι.naturality f ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.naturality f ▷ ι.app b ⊗≫ (Γ.as.app a ▷ (G.map f ≫ ι.app b) ≫
              θ.app a ◁ ι.naturality f) ⊗≫ 𝟙 _ := by
          rw [Γ.as.naturality]
          bicategory
        _ = _ := by
          rw [← whisker_exchange]
          bicategory }

end OplaxTrans
end CategoryTheory.Lax
end
