@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

open CategoryTheory

variable {J : Type u₁} [Category.{v₁} J]

variable {K : Type u₂} [Category.{v₂} K]

variable {C : Type u₃} [Category.{v₃} C]

variable {D : Type u₄} [Category.{v₄} D]

variable {E : Type u₅} [Category.{v₅} E]

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory

namespace Limits

variable {F : J ⥤ C}

namespace Cone

/-- To give an isomorphism between cocones, it suffices to give an
isomorphism between their vertices which commutes with the cocone maps. -/
@[simps]
def _root_.CategoryTheory.Limits.Cocone.ext {c c' : Cocone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, dsimp% c.ι.app j ≫ φ.hom = c'.ι.app j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      w := fun j => φ.comp_inv_eq.mpr (w j).symm }

end Cone
end Limits
end CategoryTheory
end
