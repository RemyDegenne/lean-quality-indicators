public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CentralSectionFullExtension

open scoped ComplexOrder Pointwise

open WeightedFeitExtension NormalInducedFamily

section Families

variable {L : Type*} [Group L] [Fintype L] {P Z : Subgroup L} [P.Normal] [Z.Normal]

omit [P.Normal] [Z.Normal] in
theorem kerLayerIndFam_commutator_subset_kerLayerIndFam_bot :
    kerLayerIndFam ⁅P, P⁆ P ⊆ kerLayerIndFam (⊥ : Subgroup L) P :=
  kerLayerIndFam_mono bot_le

end Families
end CentralSectionFullExtension
end CFSG.FeitThompson
end
