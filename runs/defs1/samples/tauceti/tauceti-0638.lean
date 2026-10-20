public section

open scoped WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The subspace `(A_F(D) + F) ∩ A_F` of the repartition space: the repartitions that differ
from a constant by one whose poles are bounded by `D`.  Its cokernel in `A_F` is the index of
specialty of `D`, and a Weil differential bounded by `D` is a `k`-linear form killing it. -/
noncomputable def submoduleOfAdeleFiltrationSupDiagonalRepartitions (D : Divisor k F) :
    Submodule k ↥(repartitionSpace k F) :=
  (adeleFiltration D ⊔ diagonalRepartitions k F).submoduleOf (repartitionSpace k F)

end TauCeti
end
