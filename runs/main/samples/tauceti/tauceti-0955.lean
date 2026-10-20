public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

theorem invForm_apply_apply (a b : Module.Dual K H) :
    invForm a b = a ((cartanEquivDual H).symm b) :=
  LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_cartan_nondegenerate K L H) a _

end TauCeti
end
