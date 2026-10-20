namespace P2MW.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one

set_option autoImplicit false

set_option linter.unusedSectionVars false

open Matrix MatrixGroups Subgroup MulAction ModularCurve.Period

noncomputable section

namespace BassSerreCuspDim

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (K : Type) [Field K]

def ev : (Additive Γ →+ K) →ₗ[K] (Cu Γ → K) where
  toFun φ c := φ (Additive.ofMul (genOf Γ c))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end BassSerreCuspDim
end
end P2MW.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
