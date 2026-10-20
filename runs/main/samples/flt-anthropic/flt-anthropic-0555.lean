namespace P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar

set_option autoImplicit false

open MeasureTheory AutomorphicForm Topology

open scoped TensorProduct TensorProduct.RightActions ENNReal ComplexConjugate

noncomputable section

namespace P2mKindSignCx

scoped instance instIsScalarTowerEcx : IsScalarTower ℝ Ecx Ecx :=
  ⟨fun r a b => by
    change (r • a) * b = r • (a * b)
    rw [real_smul_eq, real_smul_eq, mul_assoc]⟩

scoped instance instSMulCommClassEcx : SMulCommClass ℝ Ecx Ecx :=
  ⟨fun r a b => by
    change r • (a * b) = a * (r • b)
    rw [real_smul_eq, real_smul_eq, mul_left_comm]⟩

theorem ridE_lamE (l : ℂ) : ridE (lamE l) = l := by
  rw [lamE, ridE_tmul, one_smul]

end P2mKindSignCx
end
end P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar
