public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

variable (E : GradedExactStructure C) (P : ObjectProperty C)

section FullSubcategory

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

section Lift

variable {D : Type u'} [Category.{v'} D] {Q : ObjectProperty D} {F : C ⥤ D}
  (hP : E.toExactStructure.IsExtensionClosed P)
  (hshift : P.inverseImage E.shift.functor = P)
  (hPQ : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- **The restriction of a shift-commutation isomorphism to full subcategories.** A functor `F`
out of a graded exact category with `{1} ⋙ F ≅ F` restricts, on a shift-stable full subcategory
of its source and a full subcategory of its target containing the image, to a functor with the
same commutation isomorphism: the restricted shift is the ambient one.

This is the datum which, together with conflation-exactness, forgets the grading on the
subcategory in `TauCeti.LaurentK0.forgetGrading`. -/
noncomputable def liftCommShift (comm : E.shift.functor ⋙ F ≅ F) :
    (E.fullSubcategory P hP hshift).shift.functor ⋙ Q.lift (P.ι ⋙ F) hPQ ≅
      Q.lift (P.ι ⋙ F) hPQ := by
  rw [fullSubcategory_shift]
  exact (Q.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Q.liftCompιIso (P.ι ⋙ F) hPQ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.fullSubcategoryShiftFunctorCompιIso P hshift) F ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.ι comm ≪≫
      (Q.liftCompιIso (P.ι ⋙ F) hPQ).symm)

end Lift
end FullSubcategory
end GradedExactStructure
end TauCeti
end
