namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator

set_option autoImplicit false

noncomputable section

namespace MatChev48

open MvPolynomial Matrix

namespace SymRestriction

section DiagStructure

variable {M : Matrix (Fin 3) (Fin 3) admP}

variable (hM : IsEqv M) {a b k : Fin 3} (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k)

include hM hab hak hbk

theorem D_kb : admD a b (M k b) = -M k a := by
  rw [D_entry hM]; simp [hab.symm, hak.symm, hbk.symm]

end DiagStructure
end SymRestriction
end MatChev48
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator
