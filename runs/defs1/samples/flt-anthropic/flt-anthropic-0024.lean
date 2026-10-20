namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4

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

namespace W1xLA

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {m : ℕ} [NeZero m] {M' : ℕ} [NeZero M'] {L : Type} [Field L] [CharZero L]

section Good

variable (hmM' : Nat.Coprime m M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ξ : L)
  (ι₀ : L →+* ℂ) (hι₀ : ι₀ ξ = eq m)

def Good (X : LaurentSeries L) : Prop :=
  X ∈ KL L m M' ∧ ∃ Y ∈ KL L m M', IsImgC hmM' γ hγ (ιB ι₀ X) (ιB ι₀ Y)

end Good
end W1xLA
end
end P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4
