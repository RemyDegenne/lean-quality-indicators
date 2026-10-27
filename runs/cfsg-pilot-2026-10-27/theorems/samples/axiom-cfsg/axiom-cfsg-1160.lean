public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Module Representation

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] [Finite G]

theorem self_mem_conjClassFinset (x : G) : x ∈ conjClassFinset x :=
  mem_conjClassFinset.2 (IsConj.refl x)

end CFSG.FeitThompson
end
