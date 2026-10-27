namespace P2MW.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace W1GLB

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

section Emb

variable (ι₀ : Qb →+* ℂ)

abbrev ιB : LaurentSeries Qb →+* LaurentSeries ℂ := coeffMap ι₀

end Emb
end W1GLB
end
end P2MW.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
