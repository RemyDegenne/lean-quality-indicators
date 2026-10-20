namespace P2MW.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion

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

variable {Γ}

variable (Γ)

local notation "FFq" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

def Phi (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex] : FFq →+* K where
  toFun u := (exists_kappa_of_mem M K Γ ι hΓ hT u).choose
  map_one' := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT 1).choose_spec.2, map_one, OneMemClass.coe_one, map_one]
  map_mul' u v := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT (u * v)).choose_spec.2, map_mul,
      (exists_kappa_of_mem M K Γ ι hΓ hT u).choose_spec.2, (exists_kappa_of_mem M K Γ ι hΓ hT v).choose_spec.2,
      MulMemClass.coe_mul, map_mul]
  map_zero' := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT 0).choose_spec.2, map_zero, ZeroMemClass.coe_zero, map_zero]
  map_add' u v := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT (u + v)).choose_spec.2, map_add,
      (exists_kappa_of_mem M K Γ ι hΓ hT u).choose_spec.2, (exists_kappa_of_mem M K Γ ι hΓ hT v).choose_spec.2,
      AddMemClass.coe_add, map_add]

end Bridge
end QExpBridge
end LevelN
end ModularCurve
end
end P2MW.S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion
