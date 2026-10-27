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

/-- Affine coordinates classify the closed points of finite-dimensional
polynomial affine space over an algebraically closed field. -/
@[expose] noncomputable def mvPolynomialAffineClosedPointsEquiv
    [Finite I] [IsAlgClosed k] :
    (I → k) ≃ closedPoints (PrimeSpectrum (MvPolynomial I k)) :=
  Equiv.ofBijective mvPolynomialAffineClosedPoint
    ⟨mvPolynomialAffineClosedPoint_injective,
      mvPolynomialAffineClosedPoint_surjective⟩

end ProjectiveSpace
end
end
