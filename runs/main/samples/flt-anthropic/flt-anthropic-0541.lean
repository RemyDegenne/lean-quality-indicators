namespace P2MW.S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion

p2m_open

universe v

namespace QuaternionAlgebra

namespace OrderCasimirAux

p2m_open

variable {a b : ℚ}

section Casimir

variable {R : Type v} [Ring R]

theorem mul'_mul_one_tmul (x : R) (c : R ⊗[ℤ] R) :
    LinearMap.mul' ℤ R (c * ((1 : R) ⊗ₜ[ℤ] x)) = LinearMap.mul' ℤ R c * x := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply, mul_one, mul_assoc]
  | add c c' hc hc' => rw [add_mul, map_add, map_add, hc, hc', add_mul]

end Casimir
end OrderCasimirAux
end QuaternionAlgebra
end P2MW.S_QuaternionAlgebra_IsOrder_casimir_mul_mem_range_intCast_and_exists_casimir_mul_ne_zero
