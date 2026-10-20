@[expose] public section

universe v u v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

namespace Quiv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem pathComposition_naturality {C : Type u} {D : Type u₁}
    [Category.{v} C] [Category.{v₁} D]
    (F : C ⥤ D) : Cat.freeMap (F.toPrefunctor) ⋙ pathComposition D = pathComposition C ⋙ F :=
  Paths.ext_functor rfl (by simp)

end Quiv
end CategoryTheory
end
