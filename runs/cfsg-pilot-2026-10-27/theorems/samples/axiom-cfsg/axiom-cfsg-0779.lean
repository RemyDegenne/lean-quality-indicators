public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G]

theorem mul_mem_dadeCoset {H : G → Subgroup G} {a u : G} (hu : u ∈ H a) :
    u * a ∈ dadeCoset H a := mem_dadeCoset_iff.2 (by simpa using hu)

end CFSG.FeitThompson
end
