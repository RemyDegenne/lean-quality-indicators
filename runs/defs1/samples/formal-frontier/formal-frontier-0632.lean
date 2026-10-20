public section

noncomputable section

open AlgebraicGeometry CategoryTheory

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]

variable (ι : Type v)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- The structure morphism from polynomial projective space to a
universe-lifted copy of the coefficient spectrum. This version permits the
coefficient and coordinate types to live in independent universes. -/
def polynomialProjToSpecULift :
    Proj 𝒜 ⟶ Spec (CommRingCat.of (ULift.{v} R)) :=
  Proj.toSpecZero 𝒜 ≫
    Spec.map ((ULift.ringEquiv.trans
      (mvPolynomialDegreeZeroEquiv R ι).toRingEquiv).toCommRingCatIso.hom)

end ProjectiveSpace
end
end
