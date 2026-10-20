@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped TensorProduct

namespace UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

def quotientBialgHom : Ambient K n →ₐc[K] CoordinateRing K n r :=
  Bialgebra.Quotient.mkBialgHom (ideal K n r)

end UnitriangularStageCoordinateRing
end
end
