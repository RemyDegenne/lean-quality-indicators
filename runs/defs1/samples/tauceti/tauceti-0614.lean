public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

open LaurentPolynomial hiding C

universe w w' v v' u u'

namespace GradedExactStructure.IsResolving

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  (E : GradedExactStructure C) (P : ObjectProperty C)
  [E.toExactStructure.IsResolving P]

local instance : ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le (Q := ⊤) le_top

local notation "hP" =>
  (ExactStructure.IsResolving.isExtensionClosed (E := E.toExactStructure) (P := P))

variable (hshift : P.inverseImage E.shift.functor = P)

/-- **The graded resolution theorem for a resolving subcategory.** If `P` is resolving for the
underlying exact structure and stable under the grading shift, then inclusion induces an
isomorphism of graded Grothendieck groups as `ℤ[q,q⁻¹]`-modules. Its inverse is computed by the
Euler class of any finite `P`-resolution. -/
noncomputable def laurentResolutionEquiv :
    LaurentK0 (E.fullSubcategory P hP hshift) ≃ₗ[LaurentPolynomial ℤ] LaurentK0 E :=
  (resolutionAddEquiv E P hshift).toLinearEquiv fun c x => by
    simp only [resolutionAddEquiv_apply, map_smul]

end GradedExactStructure.IsResolving
end TauCeti
end
