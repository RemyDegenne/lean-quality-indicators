public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup CFSG.SCATWreath

variable {G : Type*} [Group G]

namespace IsModel

variable {K : Subgroup G} {n : ℕ} {mul : ℕ → ℕ → ℕ} {dec : ℕ → G}

variable (M : IsModel K n mul dec)

include M

theorem code_lt {x : G} (hx : x ∈ K) : M.code x < n := by
  rw [code, dif_pos hx]
  exact (M.surj x hx).choose_spec.1

end IsModel
end CFSG.OddStandard.AltStdSmall4.Tower
end
