public section

namespace TauCeti

namespace AlbertAlgebra

variable {R : Type*}

/-- **The trace-zero subspace `J₀` as a Lie submodule of `H₃(𝕆)` over `Der H₃(𝕆)`**, so that `J₀` is
a representation of the derivation algebra. This is the candidate fundamental representation of
`F₄`; over a base satisfying `StrongRankCondition` its dimension is `26`
(`TauCeti.AlbertAlgebra.finrank_traceZeroLieSubmodule`). -/
def traceZeroLieSubmodule (R : Type*) [CommRing R] [Invertible (2 : R)] :
    LieSubmodule R (derivationLieAlgebra R (AlbertAlgebra R)) (AlbertAlgebra R) where
  __ := traceZero R
  lie_mem {D _} _ := derivation_apply_mem_traceZero D _

end AlbertAlgebra
end TauCeti
end
