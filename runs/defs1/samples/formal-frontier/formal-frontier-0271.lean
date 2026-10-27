@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CartesianMonoidalCategory CategoryTheory.MonObj

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- The generic split-kernel section-first product specialized to the
represented upper-triangular group: `F(v,d) = e(d)i(v)`. Its multiplication
convention differs from the U-first isomorphism. Compare Milne,
*Algebraic Groups* (course notes, version 2.00), §§2.20–2.21 for the
field-base split triangular group. -/
def upperTriangularSectionFirstIso :
    unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n ≅
      upperTriangularGroupUnderlyingScheme K n :=
  splitKernelProductIso (unitriangularToUpperTriangular K n).hom.hom
    (upperTriangularDiagonalProjection K n).hom.hom
    (upperTriangularDiagonalSection K n).hom.hom
    (upperTriangularDiagonalSquare_isPullback_over K n)
    (upperTriangularSection_over K n)

end AlgebraicGeometry
end
end
