namespace P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace FBC0

section Over

variable (k : Type u) [CommRing k]

scoped instance secAlgebra (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (U : X.Opens) :
    Algebra k Γ(X, U) :=
  (toSec (X ↘ Spec (CommRingCat.of k)) U).hom.toAlgebra

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

variable (A : Type u) [CommRing A] [Algebra k A]

abbrev fstA : XA k X A ⟶ X := pullback.fst (X ↘ Spec (CommRingCat.of k)) (bc A)

end Over
end FBC0
end
end P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop
