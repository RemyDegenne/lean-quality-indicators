namespace P2MW.S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_three

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

p2m_reactivate

section Gen

variable (hmM' : Nat.Coprime m M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ξ : L)

variable (m) in

def twist (p : ℕ → PowerSeries ℤ) : LaurentSeries L :=
  ∑ j ∈ Finset.range m, HahnSeries.C (ξ ^ j) * coeffEmb L (intSeriesC ℚ (p j))

end Gen
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_exists_subgroup_finite_mem_iff_exists_eq_of_isLevelAutAt_of_eq_three
