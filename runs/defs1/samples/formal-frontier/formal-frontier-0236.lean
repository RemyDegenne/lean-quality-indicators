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

/-- A tuple as a closed point of polynomial affine space. -/
@[expose] noncomputable def mvPolynomialAffineClosedPoint (a : I → k) :
    closedPoints (PrimeSpectrum (MvPolynomial I k)) :=
  ⟨mvPolynomialAffineCoordinatePoint a,
    mvPolynomialAffineCoordinatePoint_isClosed a⟩

end ProjectiveSpace
end
end
