public section

namespace TauCeti

open Subgroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {G}

theorem closedLowerCentralSeries_eq_topologicalClosure (n : ℕ) :
    closedLowerCentralSeries G n = ((⊤ : Subgroup G).lowerCentralSeries n).topologicalClosure := by
  rw [closedLowerCentralSeries_def, pLowerCentralSeries_eq_topologicalClosure,
    pLowerCentralSeries_zero_left]

end TauCeti
end
