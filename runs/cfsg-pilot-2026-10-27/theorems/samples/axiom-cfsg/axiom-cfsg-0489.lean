namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Subgroup Pointwise

universe u

variable {G : Type*} [Group G]

namespace Prep08

theorem IsHallOf.isHallPiSubgroup {π : Set ℕ} {Y M : Subgroup G} (h : IsHallOf π Y M) :
    IsHallPiSubgroup π (Y.subgroupOf M) := h.2

end Prep08
end
end CFSG.FeitThompson
