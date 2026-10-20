@[expose] public section

set_option mathlib.tactic.category.grind true

universe v u

namespace CategoryTheory

open Category

infixr:10 " ≅ " => Iso

variable {C : Type u} [Category.{v} C] {X Y Z : C}

infixr:80 " ≪≫ " => Iso.trans

open IsIso

open IsIso

namespace Iso

@[aesop apply safe (rule_sets := [CategoryTheory]), to_dual none]
theorem inv_ext {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_id : f.hom ≫ g = 𝟙 X) : f.inv = g :=
  ((hom_comp_eq_id f).1 hom_inv_id).symm

end Iso
end CategoryTheory
end
