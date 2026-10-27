@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

variable {K ι}

variable (K ι)

def polynomialQuotient : PolynomialRing K ι →ₐ[K] PolynomialCoordinateRing K ι :=
  Ideal.Quotient.mkₐ K (polynomialIdeal K ι)

end UnitriangularCoordinateRing
end
end
