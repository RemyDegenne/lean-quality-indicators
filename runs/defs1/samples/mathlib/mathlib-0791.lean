@[expose] public section

universe v₁ v₂ u₁ u₂

open Opposite

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.Functor

variable [Category.{v₁} C]

namespace Functor

variable (C)

variable (D : Type u₂) [Category.{v₂} D]

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of functor categories induced by `leftOp` and `rightOp`.
-/
@[simps!]
def leftOpRightOpEquiv : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  functor :=
    { obj := fun F => F.unop.rightOp
      map := fun η => NatTrans.rightOp η.unop }
  inverse :=
    { obj := fun F => op F.leftOp
      map := fun η => η.leftOp.op }
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.rightOpLeftOpIso.op)
      (by
        intro F G η
        dsimp
        rw [show η = η.unop.op by simp, ← op_comp, ← op_comp]
        congr 1
        cat_disch)
  counitIso := NatIso.ofComponents fun F => F.leftOpRightOpIso

end Functor
end CategoryTheory
end
