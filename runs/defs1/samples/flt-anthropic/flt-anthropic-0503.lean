namespace P2MW.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open UpperHalfPlane Filter Topology Function

open scoped MatrixGroups Manifold Real ModularForm

noncomputable section

namespace ModularCurve

namespace LevelN

namespace QExpBridge

p2m_open

section Bridge

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M]

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring M) K] [IsScalarTower ℂ (ring M) K]
  [IsFractionRing (ring M) K]

variable (Γ : Subgroup SL(2, ℤ))

variable (ι : ℚ̄ →+* ℂ)

def iotaM : LaurentSeries ℚ̄ →+* LaurentSeries ℂ :=
  (ModularCurve.qExpand ℂ M).comp (ModularCurve.coeffMap ι)

end Bridge
end QExpBridge
end LevelN
end ModularCurve
end
end P2MW.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN
