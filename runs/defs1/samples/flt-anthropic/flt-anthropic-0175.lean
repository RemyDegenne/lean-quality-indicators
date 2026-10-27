namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

p2m_reactivate

open scoped MatrixGroups ModularForm Manifold

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup UpperHalfPlane HahnSeries

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

namespace R4GC

section Stretch

open UpperHalfPlane HahnSeries ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped MatrixGroups ModularForm Pointwise

variable {q ℓ : ℕ} [NeZero q] [NeZero ℓ] {M' : ℕ} [NeZero M']

variable (hqM' : Nat.Coprime q M') (hqlM' : Nat.Coprime (q * ℓ) M')

include hqM' hqlM'

def stretch {k : ℤ} (f : ModularForm (Γ q M') k) : ModularForm (Γ (q * ℓ) M') k :=
  restrictForm (le_stretch hqM' hqlM') (ModularForm.translate f (Dr ℓ))

end Stretch
end R4GC
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom
