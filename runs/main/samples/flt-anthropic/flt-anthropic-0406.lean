namespace P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open PDivisibleGroup Filter Topology

open scoped TensorProduct

namespace PDivStep2R

variable (p : ℕ) [Fact p.Prime]

section Reductions

variable (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)]

variable {R}

theorem resAut_mk (σ' : O p R ≃ₐ[R] O p R) (s : O p R) :
    resAut p σ' (Ideal.Quotient.mk (maxI p R) s) = Ideal.Quotient.mk (maxI p R) (σ' s) := rfl

end Reductions
end PDivStep2R
end
end P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
