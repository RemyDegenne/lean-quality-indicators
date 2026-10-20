namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain TopologicalSpace Topology Filter Set

open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mTwistedCentralizerModCentre

section Algebra

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem inverse_eq (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {e : L ⊗[K] A} (he : IsUnit e) :
    Ring.inverse e =
      AutomorphicForm.sigmaTensor K L A σ e * algebraMap A (L ⊗[K] A) (nrm K L A σ e)⁻¹ := by
  have key := mul_sigmaTensor_eq K L A σ h2 hgen e
  have hn : nrm K L A σ e ≠ 0 := (isUnit_iff_nrm_ne_zero K L A σ h2 hgen e).mp he
  obtain ⟨u, rfl⟩ := he
  rw [Ring.inverse_unit]
  apply Units.inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, key, ← map_mul, mul_inv_cancel₀ hn, map_one]

end Algebra
end P2mTwistedCentralizerModCentre
end
end P2MW.S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
