@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

theorem coordinateRingToPolynomialQuotient_comp_quotient :
    (coordinateRingToPolynomialQuotient K n).comp (quotient K n) =
      localizationToPolynomialQuotient K n := by
  exact Ideal.Quotient.liftₐ_comp _ _ _

end SpecialLinearCoordinateRing
end
end
