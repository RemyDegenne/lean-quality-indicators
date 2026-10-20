public section

namespace CategoryTheory.Functor

variable {D D' : Type*} [Category* D] [Category* D']

open MonoidalCategory

section rightAction

open MonoidalRightAction

/-- `F.OplaxLinear C` equips `F : D ⥤ D'` with a family of morphisms
`δₗ F : ∀ (c : C) (d : D), c ⊙ₗ F.obj d ⟶ F.obj (c ⊙ₗ d)`
that is natural in each variable and coherent with respect to left actions
of `C` on `D` and `D'`. -/
class OplaxRightLinear
    (F : D ⥤ D') (C : Type*) [Category* C] [MonoidalCategory C]
    [MonoidalRightAction C D] [MonoidalRightAction C D'] where
  /-- The oplax lineator morphism. -/
  δᵣ (F) (d : D) (c : C) : F.obj (d ⊙ᵣ c) ⟶ (F.obj d) ⊙ᵣ c
  δᵣ_naturality_right (F) (d : D) {c c' : C} (f : c ⟶ c') :
    F.map (d ⊴ᵣ f) ≫ δᵣ d c' =
    δᵣ d c ≫ F.obj d ⊴ᵣ f := by cat_disch
  δᵣ_naturality_left (F) {d d' : D} (f : d ⟶ d') (c : C) :
    F.map (f ⊵ᵣ c) ≫ δᵣ d' c =
    δᵣ d c ≫ F.map f ⊵ᵣ c := by cat_disch
  δᵣ_associativity (F) (d : D) (c c' : C) :
    δᵣ d (c ⊗ c') ≫ (αᵣ _ _ _).hom =
    F.map (αᵣ _ _ _).hom ≫ δᵣ (d ⊙ᵣ c) c' ≫
      δᵣ d c ⊵ᵣ c' := by cat_disch
  δᵣ_unitality_inv (F) (d : D) :
    (ρᵣ (F.obj d)).inv =
    F.map (ρᵣ d).inv ≫ δᵣ d (𝟙_ C) := by cat_disch

end rightAction
end CategoryTheory.Functor
end
