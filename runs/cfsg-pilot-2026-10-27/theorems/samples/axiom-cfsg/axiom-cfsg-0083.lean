public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

open scoped MatrixGroups

section SmulMulVec

variable {K : Type} [Field K]

theorem smulMulVec_surjective (H : SL(2, K)) {l : K} (hl : l ≠ 0) :
    Function.Surjective (smulMulVec H l) := by
  intro w
  refine ⟨((H⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec (l⁻¹ • w), ?_⟩
  rw [smulMulVec_apply, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hl, one_smul]

end SmulMulVec
end CFSG.QuasithinUnique.Lin2
end
