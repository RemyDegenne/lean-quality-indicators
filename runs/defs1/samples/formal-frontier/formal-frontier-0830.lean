@[expose] public section

open CategoryTheory

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] (A B : Cᵒᵖ ⥤ CommRingCat.{u})

/-- Forget commutativity of a whole map of ring presheaves. -/
def ringMap (theta : A ⟶ B) : ringPresheaf A ⟶ ringPresheaf B :=
  Functor.whiskerRight theta (forget₂ CommRingCat RingCat.{u})

end RingedSpaces.Modules
end
