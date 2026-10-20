public section

noncomputable section

open HomogeneousLocalization

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]

variable (ι : Type v) (i : ι)

local instance instDecidableEqCoordinates : DecidableEq ι := Classical.decEq ι

local notation "Others" => {j : ι // j ≠ i}

local notation "Poly" => MvPolynomial ι R

local notation "Q" => MvPolynomial Others R

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

local notation "Xi" => (MvPolynomial.X i : MvPolynomial ι R)

local notation "Chart" => StandardChart R ι i

/-- The affine coordinate `X j / X i` in the degree-zero homogeneous
localization at `X i`. -/
@[expose] def coordinateRatio (j : Others) : Chart :=
  Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R i) 1 (MvPolynomial.X j.1) (by
    simpa using MvPolynomial.isHomogeneous_X R j.1)

end ProjectiveSpace
end
end
