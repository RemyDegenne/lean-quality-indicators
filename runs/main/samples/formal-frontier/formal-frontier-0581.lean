@[expose] public section

universe uR uC uD uV uW

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {D : Type uD}

variable {V : Type uV} {W : Type uW}

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

theorem externalTensorCoaction_counit_comp (X : RightComodule R C V)
    (Y : RightComodule R D W) :
    (Coalgebra.counit (R := R) (A := C ⊗[R] D)).lTensor (V ⊗[R] W) ∘ₗ
        externalTensorCoaction X Y =
      (_root_.TensorProduct.rid R (V ⊗[R] W)).symm.toLinearMap := by
  -- Contracting the shuffled coefficients is natural in both module factors.
  have hnatural :
      (_root_.TensorProduct.rid R (V ⊗[R] W)).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := C ⊗[R] D)).lTensor (V ⊗[R] W) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R V C W D).toLinearMap =
        _root_.TensorProduct.map
          ((_root_.TensorProduct.rid R V).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := C)).lTensor V)
          ((_root_.TensorProduct.rid R W).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := D)).lTensor W) := by
    apply _root_.TensorProduct.ext_fourfold'
    intro v c w d
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      _root_.TensorProduct.tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul,
      _root_.TensorProduct.counit_tmul, _root_.TensorProduct.map_tmul,
      _root_.TensorProduct.rid_tmul, _root_.TensorProduct.smul_tmul',
      _root_.TensorProduct.tmul_smul, smul_smul, smul_eq_mul]
  apply _root_.TensorProduct.ext'
  intro v w
  apply (_root_.TensorProduct.rid R (V ⊗[R] W)).injective
  simpa only [externalTensorCoaction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    _root_.TensorProduct.map_tmul, X.rid_counit_coaction, Y.rid_counit_coaction,
    LinearEquiv.apply_symm_apply] using
    LinearMap.congr_fun hnatural (X.coaction v ⊗ₜ[R] Y.coaction w)

end Coalgebra.RightComodule
end
