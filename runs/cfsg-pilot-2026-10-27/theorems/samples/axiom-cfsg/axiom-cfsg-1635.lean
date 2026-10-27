namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G]

variable [Finite G]

namespace IsWitnessedPConfiguration

variable {M E W₁ W₂ : Subgroup G} (hc : IsWitnessedPConfiguration M E W₁ W₂)

include hc

theorem disjoint_cyclicTIset_conj {g : G} (hg : g ∉ W₁ ⊔ W₂) :
    Disjoint (cyclicTIset W₁ W₂) (MulAut.conj g '' cyclicTIset W₁ W₂) :=
  hc.isTIWithNormalizer_cyclicTIset.disjoint_conj_image g hg

end IsWitnessedPConfiguration
end
end CFSG.FeitThompson
