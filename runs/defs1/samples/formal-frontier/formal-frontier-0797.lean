@[expose] public section

set_option warningAsError true

noncomputable section

universe u

namespace UpperTriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The upper-triangular coordinate algebra is a localization of the polynomial
ring on retained coordinates, including over the zero ring. This specializes
`MvPolynomial.localizedCoordinateQuotientEquiv` to the preceding ideal equality;
compare Milne, *Algebraic Groups* (2017), item 2.40, over a field. -/
def localizedPolynomialEquiv :
    CoordinateRing K ι ≃ₐ[K]
      Localization.Away (MvPolynomial.eraseCoordinates K (retainedIndices ι)
        (GeneralLinearCoordinateRing.determinant K ι)) :=
  (Ideal.quotientEquivAlgOfEq K (ideal_eq_localizedCoordinateIdeal K ι)).trans
    (MvPolynomial.localizedCoordinateQuotientEquiv K (retainedIndices ι)
      (GeneralLinearCoordinateRing.determinant K ι))

end UpperTriangularCoordinateRing
end
end
