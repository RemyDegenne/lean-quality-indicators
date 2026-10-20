namespace P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one

noncomputable section

open UpperHalfPlane hiding I coe_smul

open Filter Complex MulAction Set ModularCurve.SmoothedFundamental

open scoped MatrixGroups Topology ContDiff Pointwise

namespace ModularCurve

namespace SmoothedFundamentalProof

p2m_open

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

section Sums

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (T : ℝ)

theorem finite_support_smul (τ : ℍ) :
    (Function.support fun γ : Γ =>
      ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite := by
  have hfin := finite_moving {τ} (carrierH Γ T) isCompact_singleton (isCompact_carrierH Γ T)
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro γ hγ
  refine ⟨(γ : SL(2, ℤ)) • τ, ⟨τ, rfl, rfl⟩, ?_⟩
  exact mem_carrier_of_ne_zero Γ T hγ

end Sums
end SmoothedFundamentalProof
end ModularCurve
end
end P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one
