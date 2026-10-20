namespace P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace LawA_GL

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

p2m_reactivate

section Decomp

def slPart (g : CuspidalType.GL2 q) : SL(2, ZMod q) :=
  ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (((detU g)⁻¹ : (ZMod q)ˣ) : ZMod q)], by
    rw [Matrix.det_mul, Matrix.det_fin_two_of, ← Matrix.GeneralLinearGroup.val_det_apply, one_mul, mul_zero,
      sub_zero]
    exact units_mul_inv_val (detU g)⟩

end Decomp
end LawA_GL
end
end P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm
