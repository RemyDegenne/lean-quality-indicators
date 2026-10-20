public section

open LinearMap WithConv

open scoped TensorProduct

namespace TauCeti.HopfAlgebra

namespace Point

universe u

variable (k H K : Type u) [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

/-- The multiplicative Jordan decomposition of an algebraic-group point, with the semisimple
part first and the unipotent part second. -/
noncomputable def jordanDecomposition (g : WithConv (H →ₐ[k] K)) :
    WithConv (H →ₐ[k] K) × WithConv (H →ₐ[k] K) :=
  (semisimplePart k H K g, unipotentPart k H K g)

end Point
end TauCeti.HopfAlgebra
end
