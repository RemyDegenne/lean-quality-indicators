namespace P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

universe u

noncomputable section

namespace P2mKcZp2Matrix

variable (p : ℕ) [Fact p.Prime]

scoped instance instFintypeF : Fintype (F p) := Fintype.ofFinite _

scoped instance instAlgebra : Algebra (W0 p) (O p) := (ιW p).toAlgebra

def B : Fin 2 → O p := fun i => WittVector.teichmuller p (bF p i)

end P2mKcZp2Matrix
end
end P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul
