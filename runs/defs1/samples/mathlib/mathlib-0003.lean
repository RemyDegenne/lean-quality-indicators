@[expose] public section

open Quiver (Path)

open Quiver.Path

namespace CategoryTheory

open Bicategory Category

universe v u

namespace FreeBicategory

variable {B : Type u} [Quiver.{v} B]

local instance homCategory' (a b : B) : Category (Hom a b) :=
  homCategory a b

set_option backward.isDefEq.respectTransparency.types false in
/-- A 2-isomorphism between a partially-normalized 1-morphism in the free bicategory to the
fully-normalized 1-morphism.
-/
@[simp]
def normalizeIso {a : B} :
    ∀ {b c : B} (p : Path a b) (f : Hom b c),
      (preinclusion B).map ⟨p⟩ ≫ f ≅ (preinclusion B).map ⟨normalizeAux p f⟩
  | _, _, _, Hom.of _ => Iso.refl _
  | _, _, _, Hom.id b => ρ_ _
  | _, _, p, Hom.comp f g =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫ normalizeIso (normalizeAux p f) g

end FreeBicategory
end CategoryTheory
end
