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

theorem map_dehomogenizedIdealRight [Fintype ι] (j : Others) (κ : Type w)
    (d : κ → ℕ) (F : κ → Poly) (hF : ∀ a, F a ∈ 𝒜 (d a)) :
    Ideal.map
        (algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
          (StandardChartPolynomialOverlapRight R ι i j))
        (dehomogenizedIdeal R ι j.1 κ d F hF) =
      localizedDehomogenizedIdealRight R ι i j κ d F hF := by
  rw [dehomogenizedIdeal, localizedDehomogenizedIdealRight, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, rfl⟩

end ProjectiveSpace
end
end
