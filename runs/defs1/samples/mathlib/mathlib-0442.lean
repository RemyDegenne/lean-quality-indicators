@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace Monoidal

namespace FunctorCategory

variable (F G F' G' : C ⥤ D)

/-- (An auxiliary definition for `functorCategoryMonoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
-/
@[simps]
def tensorObj : C ⥤ D where
  obj X := F.obj X ⊗ G.obj X
  map f := F.map f ⊗ₘ G.map f

end FunctorCategory
end Monoidal
end CategoryTheory
end
