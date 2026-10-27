@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

open Opposite

section Pre

variable {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G : D ⥤ E} {e : E}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A costructured arrow category on a `CostructuredArrow.pre F G e` functor is equivalent to the
costructured arrow category on F -/
@[simps]
def CostructuredArrow.preEquivalence (f : CostructuredArrow G e) :
    CostructuredArrow (pre F G e) f ≌ CostructuredArrow F f.left where
  functor := preEquivalence.functor F f
  inverse := preEquivalence.inverse F f
  unitIso := NatIso.ofComponents (fun X => isoMk (isoMk (Iso.refl _)
    (by simp)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

end Pre
end CategoryTheory
end
