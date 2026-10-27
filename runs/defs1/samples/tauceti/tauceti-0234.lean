public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- The `H`-submodule of `L` spanned by the root spaces indexed by a set `S` of roots: the weight
spaces of `L` itself at the weights the members of `S` name. -/
def rootSpaceSpan (S : Set H.root) : LieSubmodule K H L :=
  genWeightSpaceSpan H L ((fun α : H.root => (α : H → K)) '' S)

end TauCeti
end
