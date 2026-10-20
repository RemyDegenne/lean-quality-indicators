namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one

set_option autoImplicit false

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open scoped TensorProduct Quaternion

open IsDedekindDomain NumberField QuaternionAlgebra

namespace P2mSFv

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (w : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_one_mem_localBox_of_smul_mem {r : ℕ} (hr : r.Prime) (hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal)
    {α : D} {n : ℕ} (hα : ((r ^ n : ℕ) : ℤ) • α ∈ Λ) :
    α ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  haveI : CharZero (w.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (w.adicCompletion ℚ)).injective
  have hr0 : ((r : w.adicCompletion ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr.ne_zero)
  have hcast : (((r ^ n : ℕ) : ℤ) • α) = ((r ^ n : ℕ) : D) * α := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have e1 : ((r ^ n : ℕ) : D ⊗[ℚ] w.adicCompletion ℚ) *
      ((1 : D) ⊗ₜ[ℚ] ((r : w.adicCompletion ℚ) ^ n)⁻¹) = 1 := by
    rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul, Nat.cast_pow,
      mul_inv_cancel₀ hr0, ← Algebra.TensorProduct.one_def]
  have e2 : ((r ^ n : ℕ) : D ⊗[ℚ] w.adicCompletion ℚ) *
      ((1 : D) ⊗ₜ[ℚ] ((r : w.adicCompletion ℚ) ^ n)⁻¹) * (α ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) =
        ((((r ^ n : ℕ) : ℤ) • α) ⊗ₜ[ℚ] ((r : w.adicCompletion ℚ) ^ n)⁻¹) := by
    rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_one, hcast]
  rw [← one_mul (α ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)), ← e1, e2]
  exact tmul_mem_localBox Λ w hα (inv_natCast_pow_mem w hr hrw n)

end Box
end P2mSFv
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_mem_ofFiniteIdele_of_forall_finiteAdeleEvalAt_eq_one
