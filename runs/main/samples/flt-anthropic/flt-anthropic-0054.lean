namespace P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le

set_option autoImplicit false

p2m_open

namespace AlgebraicCurve

namespace RegularProlongation

namespace FIneq

p2m_open

variable {L : Type*} [Field L] {A : ValuationSubring L}

variable {F : Type*} [Field F] [Algebra L F]

variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

section resIndep

variable (R : RegularProlongation A F Fbar) {ι : Type*} (E : ι → R.integers)

theorem coe_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    ((∑ i ∈ t, constHom R (a i) * E i : R.integers) : F) = ∑ i ∈ t, (a i : L) • (E i : F) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_constHom, Algebra.smul_def]

end resIndep
end FIneq
end RegularProlongation
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_RegularProlongation_finiteDimensional_and_finrank_adjoin_residue_le
