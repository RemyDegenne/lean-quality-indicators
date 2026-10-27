set_option warningAsError true

public section

noncomputable section

open AlgebraicGeometry

open scoped LinearAlgebra.Projectivization ProjectiveSpace

namespace ProjectiveSpace

universe u v w x

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} {V : Type v} {I : Type w} [Field k]

variable [AddCommGroup V] [Module k V]

local instance instDecidableEqSymmetricAlgebraClosedPoint : DecidableEq I :=
  Classical.decEq I

/-- The basis-free cone-line map from the symmetric algebra on the dual. -/
@[expose] noncomputable def symmetricAlgebraHomogeneousCoordinateMap (v : V) :
    SymmetricAlgebra k (Module.Dual k V) →ₐ[k] Polynomial k :=
  SymmetricAlgebra.lift (dualConeLineMap v)

end ProjectiveSpace
end
end
