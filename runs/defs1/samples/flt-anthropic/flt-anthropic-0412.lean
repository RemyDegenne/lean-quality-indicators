namespace P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlueBody

section Loc

variable {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

variable (r q : R) (κ : Spec (CommRingCat.of (Localization.Away q)) ⟶ Spec (CommRingCat.of (Localization.Away r)))
  (hκ : κ ≫ ιA r = ιA q)

variable (Lr : RelativeGroupLaw (Localization.Away r) (pullback.snd f (ιA r)))

def locOne {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of (Localization.Away r))) : SchemeHomOver (w ≫ ιA r) f :=
  sqToBase (sqA f r) (Lr.one w)

end Loc
end GlueBody
end
end P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away
