namespace P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

noncomputable section

open UpperHalfPlane Filter Function

open scoped MatrixGroups Topology Manifold ModularForm Pointwise

namespace ModularCurve

namespace CuspDecayOfAux

p2m_open

scoped instance wd_neZero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : NeZero (wd Γ) :=
  ⟨Subgroup.FiniteIndex.index_ne_zero⟩

section Presentations

variable {Γ : Subgroup SL(2, ℤ)} [hTΓ : Fact (ModularGroup.T ∈ Γ)]

theorem qL_add {a : ℤ} (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods Γ), PowerSeries.coe_add]

end Presentations
end CuspDecayOfAux
end ModularCurve
end
end P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg
