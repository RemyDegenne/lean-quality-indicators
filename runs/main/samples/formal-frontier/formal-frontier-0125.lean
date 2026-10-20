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

theorem isLocalization_standardChartOverlap_right (j : Others) :
    IsLocalization.Away
      (coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩)
      (StandardChartOverlap R ι i j) := by
  have hr : coordinateRatio R ι j.1 ⟨i, Ne.symm j.2⟩ =
      Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R j.1)
        (MvPolynomial.isHomogeneous_X R i) := by
    apply HomogeneousLocalization.val_injective
    simp [coordinateRatio, Away.isLocalizationElem]
  rw [hr]
  exact Away.isLocalization_mul (MvPolynomial.isHomogeneous_X R j.1)
    (MvPolynomial.isHomogeneous_X R i) (by rw [mul_comm]) (by norm_num)

end ProjectiveSpace
end
end
