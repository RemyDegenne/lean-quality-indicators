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

section DirectCoefficientBase

variable (S : Type (max u v)) [CommRing S]

variable (κ : Type v)

local notation "ℬ" => MvPolynomial.homogeneousSubmodule κ S

/-- The structure morphism from polynomial projective space directly to its
coefficient spectrum. -/
@[expose] def polynomialProjToSpec : Proj ℬ ⟶ Spec (CommRingCat.of S) :=
  Proj.toSpecZero ℬ ≫
    Spec.map (mvPolynomialDegreeZeroEquiv S κ).toRingEquiv.toCommRingCatIso.hom

end DirectCoefficientBase
end ProjectiveSpace
end
end
