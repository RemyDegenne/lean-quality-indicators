@[expose] public section

open CategoryTheory Category ZeroObject Limits Functor

variable (C D E E' : Type*) [Category* C] [Category* D] [Category* E] [Category* E']
  (A : Type*) [AddMonoid A] [HasShift D A] [HasShift E A] [HasShift E' A]

namespace CategoryTheory

variable {C D E A}

variable (F G H : SingleFunctors C D A)

namespace SingleFunctors

variable {F G H}

variable (C D)

variable {C D}

variable (F)

/-- Given `F : SingleFunctors C D A`, and a functor `G : D ⥤ E` which commutes
with the shift by `A`, this is the "composition" of `F` and `G` in `SingleFunctors C E A`. -/
@[implicit_reducible, simps! functor shiftIso_hom_app shiftIso_inv_app]
def postcomp (G : D ⥤ E) [G.CommShift A] :
    SingleFunctors C E A where
  functor a := F.functor a ⋙ G
  shiftIso n a a' ha' :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' ha') G
  shiftIso_zero a := by
    ext X
    dsimp
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_inv_app,
      SingleFunctors.shiftIso_zero_hom_app, id_comp, assoc, ← G.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Functor.id_obj, comp_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [F.shiftIso_add_hom_app n m a a' a'' ha' ha'', Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, id_comp, assoc,
      Functor.commShiftIso_inv_naturality_assoc]
    simp only [← G.map_comp, Iso.inv_hom_id_app_assoc]

end SingleFunctors
end CategoryTheory
end
