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

/-- A vector as a closed point of the affine spectrum of the symmetric algebra
on its dual. -/
@[expose] noncomputable def symmetricAlgebraAffineClosedPoint (v : V) :
    closedPoints (PrimeSpectrum (SymmetricAlgebra k (Module.Dual k V))) :=
  ⟨symmetricAlgebraAffineCoordinatePoint v,
    symmetricAlgebraAffineCoordinatePoint_isClosed v⟩

end ProjectiveSpace
end
end
