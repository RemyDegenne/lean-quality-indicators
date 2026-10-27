namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq

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

def res1 {k : ℤ} (g : ModularForm (Γ m M') k) :
    ModularForm ((Gamma1 (m ^ 2 * M') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictForm (Subgroup.map_mono (Gamma1_le_GammaH _ _)) g

end Gen
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
