public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ExactStructure.ProjectivePresentation

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : GradedExactStructure C} {X : C}

/-- Shift every object and morphism in a relative projective presentation. -/
def shift (P : E.toExactStructure.ProjectivePresentation X) :
    E.toExactStructure.ProjectivePresentation (E.shift.functor.obj X) :=
  P.map E.shift_exact fun Q hQ ↦ by
    rw [ObjectProperty.prop_inverseImage_iff]
    exact (E.isProjective_shift_iff Q).2 hQ

end ExactStructure.ProjectivePresentation
end TauCeti
end
