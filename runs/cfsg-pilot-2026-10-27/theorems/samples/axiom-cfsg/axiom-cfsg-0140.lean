public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

namespace Setting16

variable {G : Type} [Group G] [Finite G] {Q Y : Subgroup G} {τ ω : G}

theorem om_not_mem (h : Setting16 Q Y τ ω) : ω ∉ Q := by
  intro hωQ
  have hQY : Q ≤ Y := fun a ha => h.cent_om a ha (h.comm a ha ω hωQ).symm
  have hcardle : Nat.card Q ≤ Nat.card Y := Subgroup.card_le_of_le hQY
  rw [h.card_Q, h.card_Y] at hcardle
  norm_num at hcardle

end Setting16
end CFSG.OddStandard.SmallF3.HarrisU33.S4B
end
