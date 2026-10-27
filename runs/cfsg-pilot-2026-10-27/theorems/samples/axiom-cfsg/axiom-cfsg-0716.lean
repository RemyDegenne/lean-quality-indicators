public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

namespace SecCond

variable (hc : h.SecCond y)

include hc

theorem subS_inf_normalizer : h.subS y ⊓
    normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (h.secImage y h.Q).subgroupOf (h.secSubImg y) := by
  rw [normalizer_subB, ← Sub58.inf_subgroupOf, hc.secImage_Q]

end SecCond
end Hyp52
end CFSG.ComponentClassification.GSThmB
end
