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

universe uM uN

variable {M : Type uM} {N : Type uN}

variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

@[simp] theorem externalTensor_coefficient_tmul (X : RightComodule R C M)
    (Y : RightComodule R D N) (ell : M →ₗ[R] R) (eta : N →ₗ[R] R) (m : M) (n : N) :
    (X.externalTensor Y).coefficient
        ((_root_.TensorProduct.lid R R).toLinearMap ∘ₗ _root_.TensorProduct.map ell eta)
        (m ⊗ₜ[R] n) =
      X.coefficient ell m ⊗ₜ[R] Y.coefficient eta n := by
  have hunitor :
      (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap =
        _root_.TensorProduct.map (_root_.TensorProduct.lid R C).toLinearMap
          (_root_.TensorProduct.lid R D).toLinearMap := by
    apply _root_.TensorProduct.ext_fourfold'
    intro r c s d
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      _root_.TensorProduct.tensorTensorTensorComm_tmul, LinearMap.rTensor_tmul,
      _root_.TensorProduct.map_tmul, _root_.TensorProduct.lid_tmul,
      _root_.TensorProduct.smul_tmul_smul, smul_eq_mul]
  have hnatural :
      (_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap ∘ₗ
          _root_.TensorProduct.map (ell.rTensor C) (eta.rTensor D) =
        (_root_.TensorProduct.map ell eta).rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap := by
    simpa only [LinearMap.rTensor_def, _root_.TensorProduct.map_id] using
      (_root_.TensorProduct.tensorTensorTensorComm_comp_map R ell
        (LinearMap.id : C →ₗ[R] C) eta (LinearMap.id : D →ₗ[R] D))
  have hcontract :
      (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          ((_root_.TensorProduct.lid R R).toLinearMap ∘ₗ
            _root_.TensorProduct.map ell eta).rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap =
        _root_.TensorProduct.map
          ((_root_.TensorProduct.lid R C).toLinearMap ∘ₗ ell.rTensor C)
          ((_root_.TensorProduct.lid R D).toLinearMap ∘ₗ eta.rTensor D) := by
    calc
      _ = (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          ((_root_.TensorProduct.map ell eta).rTensor (C ⊗[R] D) ∘ₗ
            (_root_.TensorProduct.tensorTensorTensorComm R M C N D).toLinearMap) := by
        simp only [LinearMap.rTensor_comp, LinearMap.comp_assoc]
      _ = (_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          ((_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap ∘ₗ
            _root_.TensorProduct.map (ell.rTensor C) (eta.rTensor D)) := by rw [hnatural]
      _ = ((_root_.TensorProduct.lid R (C ⊗[R] D)).toLinearMap ∘ₗ
          (_root_.TensorProduct.lid R R).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
          (_root_.TensorProduct.tensorTensorTensorComm R R C R D).toLinearMap) ∘ₗ
          _root_.TensorProduct.map (ell.rTensor C) (eta.rTensor D) := by
        simp only [LinearMap.comp_assoc]
      _ = _ := by rw [hunitor, ← _root_.TensorProduct.map_comp]
  simpa only [coefficient_eq, externalTensor_coaction_tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, _root_.TensorProduct.map_tmul] using
    LinearMap.congr_fun hcontract (X.coaction m ⊗ₜ[R] Y.coaction n)

end Coalgebra.RightComodule
end
