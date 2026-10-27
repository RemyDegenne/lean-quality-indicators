@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonObj

universe v₁ v₂ u₁ u₂ v u w

namespace CategoryTheory.Monoidal.GrpFunctorCategory

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
/-- A functor to group objects induces a group object in the functor category. -/
def inverseObj (A : C ⥤ Grp D) : Grp (C ⥤ D) := by
  let M := (monFunctorCategoryEquivalence C D).inverse.obj (A ⋙ Grp.forget₂Mon D)
  let inv : M.X ⟶ M.X :=
    { app X := ι[(A.obj X).X]
      naturality X Y f := (GrpObj.inv_hom (A.map f).hom.hom).symm }
  exact
  { M with
    grp :=
      { inv := inv
        left_inv := by
          ext X
          simp only [NatTrans.comp_app]
          rw [show (CartesianMonoidalCategory.lift inv (𝟙 M.X)).app X =
              CartesianMonoidalCategory.lift (inv.app X) (𝟙 (M.X.obj X)) by
                apply CartesianMonoidalCategory.hom_ext
                · rw [CartesianMonoidalCategory.lift_fst]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.fst_app] using
                    congr_app (CartesianMonoidalCategory.lift_fst inv (𝟙 M.X)) X
                · rw [CartesianMonoidalCategory.lift_snd]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.snd_app,
                    NatTrans.id_app] using
                    congr_app (CartesianMonoidalCategory.lift_snd inv (𝟙 M.X)) X]
          rw [show (SemiCartesianMonoidalCategory.toUnit M.X).app X =
              SemiCartesianMonoidalCategory.toUnit (M.X.obj X) by
                simpa only [Monoidal.tensorUnit_obj] using
                  (SemiCartesianMonoidalCategory.toUnit_unique
                    ((SemiCartesianMonoidalCategory.toUnit M.X).app X)
                    (SemiCartesianMonoidalCategory.toUnit (M.X.obj X)))]
          exact GrpObj.left_inv (A.obj X).X
        right_inv := by
          ext X
          simp only [NatTrans.comp_app]
          rw [show (CartesianMonoidalCategory.lift (𝟙 M.X) inv).app X =
              CartesianMonoidalCategory.lift (𝟙 (M.X.obj X)) (inv.app X) by
                apply CartesianMonoidalCategory.hom_ext
                · rw [CartesianMonoidalCategory.lift_fst]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.fst_app,
                    NatTrans.id_app] using
                    congr_app (CartesianMonoidalCategory.lift_fst (𝟙 M.X) inv) X
                · rw [CartesianMonoidalCategory.lift_snd]
                  simpa only [NatTrans.comp_app, Functor.Monoidal.snd_app] using
                    congr_app (CartesianMonoidalCategory.lift_snd (𝟙 M.X) inv) X]
          rw [show (SemiCartesianMonoidalCategory.toUnit M.X).app X =
              SemiCartesianMonoidalCategory.toUnit (M.X.obj X) by
                simpa only [Monoidal.tensorUnit_obj] using
                  (SemiCartesianMonoidalCategory.toUnit_unique
                    ((SemiCartesianMonoidalCategory.toUnit M.X).app X)
                    (SemiCartesianMonoidalCategory.toUnit (M.X.obj X)))]
          exact GrpObj.right_inv (A.obj X).X } }

end CategoryTheory.Monoidal.GrpFunctorCategory
end
end
