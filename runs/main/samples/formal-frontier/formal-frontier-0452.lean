@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

variable {K ι}

variable (K ι)

theorem polynomialQuotientToCoordinateRing_comp_polynomialQuotient :
    (polynomialQuotientToCoordinateRing K ι).comp (polynomialQuotient K ι) =
      polynomialToCoordinateRing K ι :=
  Ideal.Quotient.liftₐ_comp _ _ _

end UnitriangularCoordinateRing
end
end
