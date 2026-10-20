public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

omit [CharZero K] [IsTriangularizable K H L] in
@[simp]
theorem mem_integralWeightLattice_iff {lam : Dual K H} :
    lam ∈ integralWeightLattice H ↔ IsIntegralWeight lam :=
  Iff.rfl

end TauCeti
end
