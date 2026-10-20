namespace P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain TopologicalSpace Topology Filter Set

open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mTwistedCompactT

section Algebra

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A] (σ : L ≃ₐ[K] L)

def nrm (e : L ⊗[K] A) : A := pr K L A (e * AutomorphicForm.sigmaTensor K L A σ e)

end Algebra
end P2mTwistedCompactT
end
end P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
