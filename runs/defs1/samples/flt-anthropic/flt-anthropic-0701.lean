namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace W1xLBCH

variable (m : ℕ) [NeZero m]

variable {m}

section Main

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ}
  {L₀ : Type} [Field L₀] [CharZero L₀] {L : Type} [Field L] [CharZero L] (ι₀ : L₀ →+* L)

variable (τ : KL L N H ≃ₐ[L] KL L N H) (τ₀ : KL L₀ N H ≃ₐ[L₀] KL L₀ N H)

def P (x : LaurentSeries L₀) : Prop :=
  x ∈ KL L₀ N H ∧ coeffMap ι₀ x ∈ KL L N H ∧
    ∀ (h₁ : x ∈ KL L₀ N H) (h₂ : coeffMap ι₀ x ∈ KL L N H),
      ((τ ⟨coeffMap ι₀ x, h₂⟩ : KL L N H) : LaurentSeries L) =
        coeffMap ι₀ ((τ₀ ⟨x, h₁⟩ : KL L₀ N H) : LaurentSeries L₀)

end Main
end W1xLBCH
end
end P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd
