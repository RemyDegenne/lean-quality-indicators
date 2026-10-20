public section

open Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups ModularForm ComplexConjugate TauCeti.ExactDivisor

namespace TauCeti

open _root_.CuspForm TauCeti.CuspForm

variable {N Q : ℕ} [NeZero N] {W : Matrix (Fin 2) (Fin 2) ℤ}

theorem peterssonInnerCosets_atkinLehnerNormalizer_smul_atkinLehnerOperatorGamma1Cusp
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets
        (atkinLehnerNormalizer Q k • atkinLehnerOperatorGamma1Cusp hQ hQN hW k f)
        (atkinLehnerNormalizer Q k • atkinLehnerOperatorGamma1Cusp hQ hQN hW k g) =
      CuspForm.peterssonInnerCosets f g := by
  rw [CuspForm.peterssonInnerCosets_smul_left, CuspForm.peterssonInnerCosets_smul_right,
    peterssonInnerCosets_atkinLehnerOperatorGamma1Cusp, conj_atkinLehnerNormalizer, ← mul_assoc,
    ← mul_assoc, ← pow_two, atkinLehnerNormalizer_sq_mul hQ.ne', one_mul]

end TauCeti
end
