namespace P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton

set_option autoImplicit false

p2m_open

section Fold_PrincipalIdelesDiscrete

set_option autoImplicit false

p2m_open

noncomputable section

namespace NumberField

namespace FujisakiVocab

p2m_open

variable (F : Type) [Field F] [NumberField F]

theorem zero_mem_adelicZeroNbhd : (0 : AdeleRing (𝓞 F) F) ∈ adelicZeroNbhd F := by
  refine ⟨?_, fun v => ?_⟩
  · show ‖(0 : InfiniteAdeleRing F)‖ < 1
    rw [InfiniteAdeleRing.norm_eq_zero_of_not_isUnit not_isUnit_zero]
    exact zero_lt_one
  · show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem _

end FujisakiVocab
end NumberField
end
end Fold_PrincipalIdelesDiscrete
end P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton
