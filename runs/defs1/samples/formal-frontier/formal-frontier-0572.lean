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

/-- The `i`th dehomogenized ideal after restriction to the overlap with the
`j`th chart. -/
@[expose] def localizedDehomogenizedIdeal [Fintype ι] (j : Others) (κ : Type w)
    (d : κ → ℕ) (F : κ → Poly) (hF : ∀ a, F a ∈ 𝒜 (d a)) :
    Ideal (StandardChartPolynomialOverlap R ι i j) :=
  Ideal.span (Set.range fun a =>
    localizedDehomogenizedPolynomial R ι i j (F a) (hF a))

end ProjectiveSpace
end
end
