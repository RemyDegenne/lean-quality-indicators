@[expose] public section

namespace CategoryTheory.Oplax

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {F G H I : B ⥤ᵒᵖᴸ C}

namespace LaxTrans

set_option backward.defeqAttrib.useBackward true in
/-- Left whiskering of a lax natural transformation and a modification. -/
@[simps]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ η.app a ◁ (Γ.as.app a ▷ H.map f ≫ ι.naturality f) ⊗≫
                η.naturality f ▷ ι.app b ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ⊗≫ ((η.app a ≫ G.map f) ◁ Γ.as.app b ≫
              η.naturality f ▷ ι.app b) ⊗≫ 𝟙 _ := by
          rw [Γ.as.naturality]
          bicategory
        _ = _ := by
          rw [whisker_exchange]
          bicategory }

end LaxTrans
end CategoryTheory.Oplax
end
