namespace P2MW.S_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem

set_option autoImplicit false

open MeasureTheory AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace ProperUnifBridge

open scoped TensorProduct TensorProduct.RightActions

open ProperUnifCore

def ρi : GL (Fin 2) ℂ →* GL (Fin 2) TT := Matrix.GeneralLinearGroup.map ρr.symm.toRingHom

end ProperUnifBridge
end
end P2MW.S_AutomorphicForm_exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem
