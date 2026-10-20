public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace GradedConflationExact

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

variable (E : GradedExactStructure C) (P : ObjectProperty C)

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

section Lift

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : GradedExactStructure D} {Q : ObjectProperty D}
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts] {F : C ⥤ D} [F.Additive]
  (hP : E.toExactStructure.IsExtensionClosed P)
  (hQ : E'.toExactStructure.IsExtensionClosed Q)
  (hPshift : P.inverseImage E.shift.functor = P)
  (hQshift : Q.inverseImage E'.shift.functor = Q)

local instance : Q.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero Q

@[simp]
theorem lift_commShift_hom_app_hom (hF : GradedConflationExact E E' F)
    (hPQ : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) (X : P.FullSubcategory) :
    HEq ((hF.lift E P hP hQ hPshift hQshift hPQ).commShift.hom.app X).hom
      (hF.commShift.hom.app X.obj) := by
  simp [lift, GradedExactStructure.fullSubcategory,
    GradedExactStructure.fullSubcategoryShift, Equivalence.congrFullSubcategory]

end Lift
end GradedConflationExact
end TauCeti
end
