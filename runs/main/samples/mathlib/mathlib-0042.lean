@[expose] public section

universe w v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

namespace CofibrantObject

set_option backward.isDefEq.respectTransparency false in
lemma exists_bifibrant_map {X₁ X₂ : CofibrantObject C} (f : X₁ ⟶ X₂) :
    ∃ (g : bifibrantResolutionObj X₁ ⟶ bifibrantResolutionObj X₂),
      iBifibrantResolutionObj X₁ ≫ (BifibrantObject.ιCofibrantObject.map g) =
      f ≫ iBifibrantResolutionObj X₂ := by
  have sq : CommSq (ι.map (f ≫ iBifibrantResolutionObj X₂))
    (iBifibrantResolutionObj X₁).hom (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨BifibrantObject.homMk sq.lift, by cat_disch⟩

end CofibrantObject
end HomotopicalAlgebra
end
