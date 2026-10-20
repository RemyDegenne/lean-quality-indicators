public section

namespace TauCeti

universe u v w

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule.{u})

@[simp]
theorem coordinatePower_toFiniteBilinearModule (ι : Type v) [Fintype ι] :
    (A.coordinatePower ι).toFiniteBilinearModule =
      A.toFiniteBilinearModule.coordinatePower ι :=
  (rfl)

end FiniteQuadraticModule
end TauCeti
end
