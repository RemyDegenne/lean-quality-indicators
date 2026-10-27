public section

namespace TauCeti

namespace IntegralLattice

open Finset Matrix Module

variable (n : ℕ)

/-- The dot product of `ℚ^{n+1}`, restricted to the zero-sum hyperplane. -/
noncomputable def zeroSumForm :
    LinearMap.BilinForm ℚ (singleParityCheckCode ℚ (Fin (n + 1))) :=
  LinearMap.BilinForm.restrict (dotProductBilin ℚ ℚ) (singleParityCheckCode ℚ (Fin (n + 1)))

end IntegralLattice
end TauCeti
end
