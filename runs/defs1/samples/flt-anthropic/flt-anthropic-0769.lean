namespace P2MW.S_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

open scoped TensorProduct TensorProduct.RightActions

open MeasureTheory Filter Topology AutomorphicForm AutomorphicForm.GL2Real

open scoped ContDiff

noncomputable section

namespace P2mHCLimR

section BoxS

def chart (p : (ℝ × ℝ × ℝ) × ℝ) : GL (Fin 2) ℝ := triU p.1 * rotGL p.2

end BoxS
end P2mHCLimR
end
end P2MW.S_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform
