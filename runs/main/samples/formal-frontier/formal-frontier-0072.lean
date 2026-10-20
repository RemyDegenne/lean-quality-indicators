public section

set_option warningAsError true

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {N G Q : C} [GrpObj G] [GrpObj Q]
  (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q] (e : Q ⟶ G)
  (hN : IsPullback i (toUnit N) q η[Q]) (he : e ≫ q = 𝟙 Q)

include hN he

variable [GrpObj N] [IsMonHom i]

variable [IsMonHom e]

theorem splitKernelProductIso_mul_lift {T : C} (n n' : T ⟶ N) (a a' : T ⟶ Q) :
    lift ((lift (a'⁻¹) n ≫ splitKernelConj i q e hN he) * n') (a * a') ≫
        (splitKernelProductIso i q e hN he).hom =
      (lift n a ≫ (splitKernelProductIso i q e hN he).hom) *
        (lift n' a' ≫ (splitKernelProductIso i q e hN he).hom) := by
  simp [splitKernelProductIso_hom, MonObj.comp_mul,
    MonObj.mul_comp, GrpObj.inv_comp]
  group

end CategoryTheory
end
