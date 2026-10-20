@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- Bialgebra quotient induced by the defining Hopf ideal. -/
def unitriangularQuotientBialgHom :
    GeneralLinearCoordinateRing.CoordinateRing K n →ₐc[K]
      UnitriangularCoordinateRing.CoordinateRing K n :=
  Bialgebra.Quotient.mkBialgHom (ideal K n)

end AlgebraicGeometry
end
end
