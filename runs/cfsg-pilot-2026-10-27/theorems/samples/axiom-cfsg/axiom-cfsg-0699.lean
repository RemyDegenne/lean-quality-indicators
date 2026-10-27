public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData

open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Cfg

variable {d : Datum A} {α : ℕ} (K : Cfg d α)

include K

theorem q_mem_Q : d.q ∈ d.Q := d.q_mem_Q K.h

end Cfg
end CFSG.OddStandard.ChengHeld.Excl2
end
