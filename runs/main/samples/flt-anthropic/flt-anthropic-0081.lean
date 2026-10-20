namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

open UpperHalfPlane

open scoped ModularForm Manifold

namespace PU1P3

theorem det_U (v : ℝ) : (U v).det.val = 1 := by
  simp [U, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

end PU1P3
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv
