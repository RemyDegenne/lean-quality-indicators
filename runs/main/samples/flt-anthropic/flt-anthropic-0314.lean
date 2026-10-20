namespace P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor

attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam

set_option autoImplicit false

set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Function

open scoped ModularForm MatrixGroups

noncomputable section

namespace ALLiP

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section API

theorem map_int_mul (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

end API
end ALLiP
end
end P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
