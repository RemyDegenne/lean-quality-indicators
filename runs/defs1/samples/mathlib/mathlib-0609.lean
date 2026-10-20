@[expose] public section

namespace CategoryTheory

universe v u

variable {T : Type u} [Category.{v} T]

namespace Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable (C D)

variable {C D}

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence of categories `Arrow C ≌ Arrow D` induced by an equivalence `C ≌ D`. -/
@[simps]
def mapArrowEquivalence (e : C ≌ D) : Arrow C ≌ Arrow D where
  functor := e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unitIso := Functor.mapIso (mapArrowFunctor C C) e.unitIso
  counitIso := Functor.mapIso (mapArrowFunctor D D) e.counitIso

end Functor
end CategoryTheory
end
