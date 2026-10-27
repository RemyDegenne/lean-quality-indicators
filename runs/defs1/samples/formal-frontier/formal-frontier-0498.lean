@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

variable {K ι}

variable (K ι)

/-- The unlocalized all-entry presentation of Milne's `U_n` (item 2.9) is
the free polynomial algebra on exactly the strictly upper entries. This
algebra equivalence does not assert an additive-group-scheme identification
or compatibility with Hopf structures. -/
def polynomialFreeEquiv : PolynomialCoordinateRing K ι ≃ₐ[K] FreeCoordinateRing K ι :=
  AlgEquiv.ofAlgHom (polynomialQuotientToFree K ι)
    (freeToPolynomialQuotient K ι)
    (polynomialQuotientToFree_comp_freeToPolynomialQuotient K ι)
    (freeToPolynomialQuotient_comp_polynomialQuotientToFree K ι)

end UnitriangularCoordinateRing
end
end
