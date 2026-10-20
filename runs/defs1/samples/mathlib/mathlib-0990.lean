@[expose] public section

namespace CategoryTheory

open Opposite

universe w' w v₁ v₂ u₁ u₂

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

variable {C D}

namespace Profunctor

set_option backward.defeqAttrib.useBackward true in
/-- Construct a natural transformation between profunctors from a `ProfunctorCore.Hom`. -/
@[simps]
def ofHom {P Q : ProfunctorCore.{w} C D} (f : P.Hom Q) : ofCore P ⟶ ofCore Q where
  app X := { app Y := f.app X (unop Y) }

end Profunctor
end CategoryTheory
end
