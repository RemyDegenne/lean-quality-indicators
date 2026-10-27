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

/-- The degree-zero homogeneous localization at `X i` is the polynomial ring
in the affine coordinates `X j / X i`, for `j ≠ i`. -/
@[expose] def standardChartEquiv [Fintype ι] : Q ≃ₐ[R] Chart :=
  AlgEquiv.ofBijective (MvPolynomial.aeval (coordinateRatio R ι i))
    ⟨by exact chartMap_injective R ι i, by exact chartMap_surjective R ι i⟩

end ProjectiveSpace
end
end
