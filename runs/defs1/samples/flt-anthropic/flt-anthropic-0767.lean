namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise

open QuaternionAlgebra CerednikDrinfeld

namespace Q1Classify13

variable {a b : ℚ}

noncomputable def orb (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℂ) : ℍ[ℚ, a, b] →ₗ[ℚ] (Fin 2 → ℂ) where
  toFun x := (ιC ι x).mulVec v
  map_add' x y := by rw [ιC_add, Matrix.add_mulVec]
  map_smul' r x := by
    rw [ιC_smul, Matrix.smul_mulVec, RingHom.id_apply, Rat.cast_smul_eq_qsmul]

end Q1Classify13
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
