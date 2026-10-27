namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {M E W₁ W₂ : Subgroup G}

namespace IsTypeIV

variable (h : IsTypeIV M)

include h

theorem isTIWithNormalizer_fittingRawSharp : IsTIWithNormalizer (fittingRawSharp M) M := by
  obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
  exact hc.isTIWithNormalizer_fittingRawSharp

end IsTypeIV
end
end CFSG.FeitThompson
