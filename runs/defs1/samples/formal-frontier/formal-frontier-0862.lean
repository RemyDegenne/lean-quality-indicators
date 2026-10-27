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

attribute [instance] isLocalization_standardChartOverlap

/-- The polynomial presentation of the overlap of the `i`th and `j`th
standard charts, obtained by inverting the variable representing `X j / X i`. -/
abbrev StandardChartPolynomialOverlap (j : Others) :=
  Localization.Away (MvPolynomial.X j : Q)

end ProjectiveSpace
end
end
