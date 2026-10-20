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

/-- The affine dehomogenization of a homogeneous polynomial on the `i`th
standard chart, characterized by the fraction `F / X i ^ d`. -/
@[expose] def dehomogenizedPolynomial [Fintype ι] {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) : Q :=
  (standardChartEquiv R ι i).symm
    (homogeneousPolynomialOnChart R ι i F hF)

end ProjectiveSpace
end
end
