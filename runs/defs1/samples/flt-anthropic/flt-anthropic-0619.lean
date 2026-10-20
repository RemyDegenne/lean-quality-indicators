namespace P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

set_option synthInstance.maxHeartbeats 1600000

section Fold_TateSDecomp

set_option autoImplicit false

p2m_open

open scoped NNReal

noncomputable section

namespace NumberField

namespace TateGlobal

p2m_open

variable {F : Type} [Field F] [NumberField F]

def unitsOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (AdeleRing (𝓞 F) F)ˣ where
  carrier := {x | (x : AdeleRing (𝓞 F) F) ∈ integralOutside S ∧
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S}
  one_mem' := ⟨by simpa using one_mem_integralOutside S, by simpa using one_mem_integralOutside S⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · simpa using mul_mem_integralOutside hx hy
    · simpa [mul_inv_rev] using mul_mem_integralOutside hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨hx', by simpa using hx⟩

end TateGlobal
end NumberField
end
end Fold_TateSDecomp
end P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe
