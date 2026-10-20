namespace P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ}

section Slash

variable (hmM' : Nat.Coprime m M')

include hmM'

def sl {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (f : ModularForm (Γ m M') k) :
    ModularForm (Γ m M') k :=
  restrictForm (le_conj hmM' hγ) (ModularForm.translate f (conjElemN m γ))

end Slash
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase
