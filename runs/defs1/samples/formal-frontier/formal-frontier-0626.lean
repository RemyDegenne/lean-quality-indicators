set_option warningAsError true

public section

noncomputable section

open AlgebraicGeometry

namespace ProjectiveSpace

universe u v w

variable {k : Type u} {V : Type v} {I : Type w} [Field k]

variable [AddCommGroup V] [Module k V]

local instance instDecidableEqSymmetricAlgebraAffineClosedPoint : DecidableEq I :=
  Classical.decEq I

/-- A linear equivalence induces the contravariant equivalence on affine
closed points of the symmetric algebras on the dual spaces. -/
@[expose] noncomputable def symmetricAlgebraAffineClosedPointsEquivOfLinearEquiv
    {W : Type w} [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) :
    closedPoints
        (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V))) ≃
      closedPoints
        (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k W))) :=
  primeSpectrumClosedPointsEquivOfRingEquiv
    (SymmetricAlgebra.congr e.dualMap).symm.toRingEquiv

end ProjectiveSpace
end
end
