@[expose] public section

universe t w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section

variable (X : C) (Y : C) (e : X ≅ Y) (κ : Cardinal.{w}) [Fact κ.IsRegular]

section

variable {J : Type*} [Category* J] {D : J ⥤ C}

variable {X}

set_option backward.defeqAttrib.useBackward true in
lemma IsCardinalPresentable.exists_commSq_of_isColimit
    {J : Type*} [Category* J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {X Y : J ⥤ C} (f : X ⟶ Y) {c₁ : Cocone X} {c₂ : Cocone Y}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (f' : c₁.pt ⟶ c₂.pt) (hf' : ∀ (j : J), c₁.ι.app j ≫ f' = f.app j ≫ c₂.ι.app j)
    ⦃X' Y' : C⦄ ⦃t : X' ⟶ Y'⦄ ⦃l : X' ⟶ c₁.pt⦄ ⦃r : Y' ⟶ c₂.pt⦄
    [IsCardinalPresentable X' κ] [IsCardinalPresentable Y' κ]
    (sq : CommSq t l r f') :
    ∃ (j : J) (l' : X' ⟶ X.obj j) (r' : Y' ⟶ Y.obj j),
      l' ≫ c₁.ι.app j = l ∧ r' ≫ c₂.ι.app j = r ∧ CommSq t l' r' (f.app j) := by
  have := isFiltered_of_isCardinalFiltered J κ
  obtain ⟨j₁, l', hl'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc₁ l
  obtain ⟨j₂, r', hr'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc₂ r
  obtain ⟨j₃, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs j₁ j₂
  obtain ⟨j₄, c, hc⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
    hc₂ (t ≫ r' ≫ Y.map b) (l' ≫ X.map a ≫ f.app j₃) (by
      simp [dsimp% hr', sq.w, ← dsimp% hf', reassoc_of% dsimp% hl'])
  exact ⟨j₄, l' ≫ X.map a ≫ X.map c, r' ≫ Y.map b ≫ Y.map c, by cat_disch⟩

end
end
end CategoryTheory
end
