public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

variable [Preadditive C]

/-- **Two retracts whose idempotents sum to the identity split an object as a biproduct.** Its
comparison map and inverse are read off by `TauCeti.isoBiprodOfRetracts_hom` and
`TauCeti.isoBiprodOfRetracts_inv`. -/
noncomputable def isoBiprodOfRetracts [HasBinaryBiproducts C] {X Y Z : C} (i₁ : Y ⟶ X) (r₁ : X ⟶ Y)
    (i₂ : Z ⟶ X) (r₂ : X ⟶ Z) (h₁ : i₁ ≫ r₁ = 𝟙 Y) (h₂ : i₂ ≫ r₂ = 𝟙 Z)
    (h : r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 X) : X ≅ Y ⊞ Z := by
  -- `i₁` and `i₂` are split monomorphisms, so orthogonality can be checked after composing with
  -- them, where `h` and the two retraction identities settle it.
  haveI : IsSplitMono i₁ := ⟨⟨r₁, h₁⟩⟩
  haveI : IsSplitMono i₂ := ⟨⟨r₂, h₂⟩⟩
  have key₁ : i₁ ≫ (r₁ ≫ i₁ + r₂ ≫ i₂) = i₁ := by rw [h, Category.comp_id]
  have key₂ : i₂ ≫ (r₁ ≫ i₁ + r₂ ≫ i₂) = i₂ := by rw [h, Category.comp_id]
  simp only [Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂, add_eq_left,
    add_eq_right] at key₁ key₂
  have horth₁ : i₁ ≫ r₂ = 0 := by rw [← cancel_mono i₂, Category.assoc, key₁, zero_comp]
  have horth₂ : i₂ ≫ r₁ = 0 := by rw [← cancel_mono i₁, Category.assoc, key₂, zero_comp]
  exact
    { hom := biprod.lift r₁ r₂
      inv := biprod.desc i₁ i₂
      hom_inv_id := by rw [biprod.lift_desc, h]
      inv_hom_id := by
        refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
          simp [h₁, h₂, horth₁, horth₂] }

end TauCeti
end
