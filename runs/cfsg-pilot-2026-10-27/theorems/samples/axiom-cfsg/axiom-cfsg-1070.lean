public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15422

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Hyp15422

variable {s : Setting15419 G T}

theorem triple (h : Hyp15422 s) : F6.IsGoldschmidtTripleIn s.I s.G₁ s.G₂ :=
  isGoldschmidtTripleIn s h.hyp h.h12 h.h19 (isSylowTwoOf_T₀ s h.h19 h.h20)

end Hyp15422
end L15422
end CFSG.Quasithin.EmptyFaithfulMultiple
end
