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

/-- The `j`th dehomogenized ideal after restriction to the overlap with the
`i`th chart, in the right polynomial presentation. -/
@[expose] def localizedDehomogenizedIdealRight [Fintype ι] (j : Others) (κ : Type w)
    (d : κ → ℕ) (F : κ → Poly) (hF : ∀ a, F a ∈ 𝒜 (d a)) :
    Ideal (StandardChartPolynomialOverlapRight R ι i j) :=
  Ideal.span (Set.range fun a =>
    localizedDehomogenizedPolynomialRight R ι i j (F a) (hF a))

end ProjectiveSpace
end
end
