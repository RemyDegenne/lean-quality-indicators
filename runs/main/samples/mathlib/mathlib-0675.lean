@[expose] public section

universe v' v u' u

namespace CategoryTheory

open Opposite Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma pullHom_pullHom
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) ⦃Y'' : C⦄ (g' : Y'' ⟶ Y') (g'f₁ : Y'' ⟶ X₁)
    (g'f₂ : Y'' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch)
    (hg'f₁ : g' ≫ gf₁ = g'f₁ := by cat_disch) (hg'f₂ : g' ≫ gf₂ = g'f₂ := by cat_disch) :
    pullHom (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) g' g'f₁ g'f₂ hg'f₁ hg'f₂ =
      pullHom φ (g' ≫ g) g'f₁ g'f₂ := by
  dsimp [pullHom]
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc,
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ _ rfl (by aesop),
    F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc _ _ _ _ _ _ _ rfl (by aesop)]
  simp [mapComp'_inv_naturality_assoc, ← reassoc_of% Cat.Hom₂.comp_app]

end LocallyDiscreteOpToCat
end Pseudofunctor
end CategoryTheory
end
