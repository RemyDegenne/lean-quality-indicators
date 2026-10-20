@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category* C]

namespace Pretriangulated

variable [HasShift C ℤ]

open Pretriangulated.Opposite

variable {C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma opShiftFunctorEquivalence_add_unitIso_hom_app_eq
    (X : Cᵒᵖ) (m n p : ℤ) (h : m + n = p := by lia) :
    (opShiftFunctorEquivalence C p).unitIso.hom.app X =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫
      (((opShiftFunctorEquivalence C m).unitIso.hom.app (X⟦n⟧)).unop⟦n⟧').op ≫
      ((shiftFunctorAdd' C m n p h).hom.app _).op ≫
      (((shiftFunctorAdd' Cᵒᵖ n m p (by lia)).inv.app X).unop⟦p⟧').op := by
  rw [opShiftFunctorEquivalence_unitIso_hom_app X p (-p),
    opShiftFunctorEquivalence_unitIso_hom_app X n (-n),
    opShiftFunctorEquivalence_unitIso_hom_app (X⟦n⟧) m (-m)]
  rw [shiftFunctorAdd'_op_inv_app _ n m p (by lia) _ _ _ (add_neg_cancel n)
    (add_neg_cancel m) (add_neg_cancel p),
    shiftFunctorCompIsoId_add'_hom_app _ _ _ _ _ _
      (neg_add_cancel m) (neg_add_cancel n) (neg_add_cancel p) h]
  simp [shiftFunctorOpIso, shiftFunctor_op_obj, shiftFunctor_op_map _ m (-m), ← op_comp,
    (shiftFunctorAdd' C m n p h).hom.naturality]

end Pretriangulated
end CategoryTheory
end
