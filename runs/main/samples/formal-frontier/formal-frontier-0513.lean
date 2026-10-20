public section

noncomputable section

open HomogeneousLocalization

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v w

variable (R : Type u) [CommRing R]

variable (ι : Type v) (i : ι)

local instance instDecidableEqHomogeneousIdealCoordinates : DecidableEq ι := Classical.decEq ι

local notation "Others" => {j : ι // j ≠ i}

local notation "Poly" => MvPolynomial ι R

local notation "Q" => MvPolynomial Others R

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

theorem standardChartHomogeneousIdealOverlapEquiv_coordinate_other [Fintype ι]
    (j : Others) (κ : Type w) (d : κ → ℕ) (F : κ → Poly)
    (hF : ∀ a, F a ∈ 𝒜 (d a)) (k : ι) (hki : k ≠ i) (hkj : k ≠ j.1) :
    standardChartHomogeneousIdealOverlapEquiv R ι i j κ d F hF
        (Ideal.Quotient.mk _
          (algebraMap Q (StandardChartPolynomialOverlap R ι i j)
            (MvPolynomial.X ⟨k, hki⟩))) =
      Ideal.Quotient.mk _
          (algebraMap (MvPolynomial {l : ι // l ≠ j.1} R)
            (StandardChartPolynomialOverlapRight R ι i j)
            (MvPolynomial.X ⟨k, hkj⟩)) *
        Ideal.Quotient.mk _
          (standardChartPolynomialTransitionUnit R ι i j) := by
  rw [standardChartHomogeneousIdealOverlapEquiv_mk,
    standardChartPolynomialTransition_other, map_mul]

end ProjectiveSpace
end
end
