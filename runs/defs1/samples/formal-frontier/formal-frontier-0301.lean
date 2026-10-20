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

/-- The polynomial chart presentation localized at `X j / X i` agrees with
the degree-zero homogeneous localization at `X i * X j`. -/
@[expose] noncomputable def standardChartPolynomialOverlapEquiv [Fintype ι] (j : Others) :
    StandardChartPolynomialOverlap R ι i j ≃ₐ[R]
      StandardChartOverlap R ι i j where
  __ := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (MvPolynomial.X j : Q))
    (T := Submonoid.powers (coordinateRatio R ι i j))
    (StandardChartPolynomialOverlap R ι i j)
    (StandardChartOverlap R ι i j)
    (standardChartEquiv R ι i).toRingEquiv
    (by
      rw [Submonoid.map_powers]
      congr 1
      exact standardChartEquiv_X R ι i j)
  commutes' r := by
    change IsLocalization.ringEquivOfRingEquiv
        (M := Submonoid.powers (MvPolynomial.X j : Q))
        (T := Submonoid.powers (coordinateRatio R ι i j))
        (StandardChartPolynomialOverlap R ι i j)
        (StandardChartOverlap R ι i j)
        (standardChartEquiv R ι i).toRingEquiv
        (standardChartEquiv_map_powers R ι i j)
        (algebraMap Q (StandardChartPolynomialOverlap R ι i j)
          (MvPolynomial.C r)) =
      standardChartOverlapMap R ι i j
        (algebraMap R (StandardChart R ι i) r)
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    congr 1
    exact (standardChartEquiv R ι i).commutes r

end ProjectiveSpace
end
end
