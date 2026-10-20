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

/-- The affine evaluation ideal attached to a vector. -/
@[expose] noncomputable def symmetricAlgebraAffineCoordinateIdeal (v : V) :
    Ideal (SymmetricAlgebra k (Module.Dual k V)) :=
  RingHom.ker (symmetricAlgebraAffineCoordinateMap v).toRingHom

end ProjectiveSpace
end
end
