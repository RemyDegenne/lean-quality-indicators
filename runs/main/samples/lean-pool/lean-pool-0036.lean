@[expose] public section

attribute [instance] starAlgebra.toRing

attribute [instance] starAlgebra.toAlgebra

attribute [instance] starAlgebra.toStarRing

attribute [instance] starAlgebra.toStarModule

export starAlgebra (modAut)

open scoped InnerProductSpace

open scoped TensorProduct

attribute [instance] QuantumSet.toInnerProductAlgebra

attribute [reducible, instance] QuantumSet.nIsFintype

attribute [reducible, instance] QuantumSet.nIsDecidableEq

export QuantumSet (n onb k)

variable {A : Type*} [ha : _root_.starAlgebra A]

variable {B : Type*} [hb : _root_.starAlgebra B]

open QuantumSet

local notation "|" a "⟩⟨" b "|" => @rankOne ℂ _ _ _ _ _ _ _ a b

open scoped TensorProduct

open scoped Matrix

theorem Psi_inv_comp_swap_lTensor_op_comp_comul_eq_rmul [QuantumSet A] :
    (Psi 0 (k A + 1)).symm.toLinearMap
      ∘ₗ (tenSwap ℂ).toLinearMap
      ∘ₗ (LinearMap.lTensor A (op ℂ).toLinearMap)
      ∘ₗ Coalgebra.comul =
    rmul := by
  ext x y
  apply ext_inner_left ℂ
  intro z
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Psi_symm_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul x : A ⊗[ℂ] A)
  rw [← h]
  simp_rw [map_sum, LinearMap.sum_apply, inner_sum, LinearMap.lTensor_tmul,
    LinearEquiv.coe_toLinearMap, op_apply, tenSwap_apply', PsiInvFun_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, neg_zero, starAlgebra.modAut_zero,
    AlgEquiv.one_apply, MulOpposite.unop_op, inner_smul_right, neg_add,
    ← inner_conj_symm _ y, ← sub_eq_add_neg, ← QuantumSet.inner_modAut_right_conj,
    inner_conj_symm, ← TensorProduct.inner_tmul, ← inner_sum, h,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_right,
    LinearMap.mul'_apply, rmul_apply, QuantumSet.inner_star_left,
    starAlgebra.modAut_star, modAut_apply_modAut, add_neg_cancel,
    starAlgebra.modAut_zero, star_star, AlgEquiv.one_apply]

end
