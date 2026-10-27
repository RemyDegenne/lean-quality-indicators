namespace P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain TopologicalSpace Topology Filter Set

open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mTwistedCompactT

section Place

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

def Xi (Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Fin 2 → Fin 2 → Fin (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) →
      v.adicCompletion K :=
  fun i j => crd K L v (Y i j)

end Place
end P2mTwistedCompactT
end
end P2MW.S_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_sigmaConj_mul_mem_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
