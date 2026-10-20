@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

variable {K ι}

variable (K ι)

omit [Fintype ι] in
theorem polynomialQuotient_lower (i j : ι) (h : j < i) :
    polynomialQuotient K ι (MvPolynomial.X (i, j)) = 0 := by
  have hz : polynomialQuotient K ι (polynomialRelation K ι i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, j), rfl⟩)
  simpa [polynomialRelation, h] using hz

end UnitriangularCoordinateRing
end
end
