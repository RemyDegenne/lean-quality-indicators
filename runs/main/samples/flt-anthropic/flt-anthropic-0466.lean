namespace P2MW.S_NumberField_mixedEmbedding_gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_open

open scoped ENNReal

noncomputable section

namespace NumberField

namespace GramMixed

p2m_open

variable (K : Type) [Field K] [NumberField K]

open scoped Classical

theorem sqrt_abs_det_gram_sB :
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin (Fintype.card (index K)) =>
        Algebra.trace ℝ (mixedSpace K) (sB K i * sB K j)).det|) = 2 ^ nrComplexPlaces K := by
  have : (Matrix.of fun i j : Fin (Fintype.card (index K)) =>
        Algebra.trace ℝ (mixedSpace K) (sB K i * sB K j)) =
      (Matrix.of fun x y : index K => Algebra.trace ℝ (mixedSpace K) (stdBasis K x * stdBasis K y)).submatrix
        (Fintype.equivFin (index K)).symm (Fintype.equivFin (index K)).symm := by
    ext i j
    simp [sB, Module.Basis.reindex_apply]
  rw [this, Matrix.det_submatrix_equiv_self, sqrt_abs_det_gram_std, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

end GramMixed
end NumberField
end
end P2MW.S_NumberField_mixedEmbedding_gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume
