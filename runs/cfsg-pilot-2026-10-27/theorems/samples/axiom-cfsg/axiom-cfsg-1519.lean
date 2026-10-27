public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MulAction Pointwise Subgroup

variable {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {L Z : Subgroup G} {h : ℕ}

namespace IsTINormalCentralSection

variable (hs : IsTINormalCentralSection p P L Z h) {z x y g : G}

include hs

theorem Z_le : Z ≤ L := hs.Z_le_sylow.trans hs.sylow_le

end IsTINormalCentralSection
end CFSG.FeitThompson
end
