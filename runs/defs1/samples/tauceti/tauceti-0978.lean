public section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C} [e.functor.Additive] [e.functor.Linear k]

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

variable (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
  (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
  (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
  (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
  (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)

/-- The left numerical quotient of the first Laurent-module Grothendieck group for the graded
Ext-Euler pairing. -/
abbrev GradedExtEulerLeftNumericalQuotient :=
  LeftNumericalQuotient (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

end TauCeti
end
