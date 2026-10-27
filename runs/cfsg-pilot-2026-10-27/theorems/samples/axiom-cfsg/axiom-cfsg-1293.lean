public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance

open scoped Pointwise

set_option linter.unusedSectionVars false

section KQ1Abstract

variable {Lb : Type} [Group Lb] [Finite Lb]

theorem KQ1_conj_eq_one_iff (g : Lb) :
    (MulAut.conj g : MulAut Lb) = 1 ↔ g ∈ Subgroup.center Lb := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun σ : MulAut Lb => σ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]; group

end KQ1Abstract
end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210Ns
end
