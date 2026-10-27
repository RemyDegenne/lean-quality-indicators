set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

section BaseChange

variable (A : Type u) [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B]

abbrev kaehlerH0baseChangeMap :
    (𝒱.kaehlerSections c).H0 →ₛₗ[algebraMap R A]
      ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H0 :=
  (HomOver.baseChange 𝒱 c A).kaehlerH0map

end BaseChange
end AlgebraicGeometry.Scheme.TwoAffineOpenCover
end
