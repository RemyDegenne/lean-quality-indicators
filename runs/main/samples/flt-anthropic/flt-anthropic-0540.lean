namespace P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

p2m_open

namespace ExtCitation

namespace LocalLevel

namespace ResFC

p2m_open

section Chi

variable {G : Type} [Group G] {N : ℕ}

variable [NeZero N]

theorem chiCarry_eq_ite (χ : G →* Multiplicative (ZMod N)) (g h : G) :
    chiCarry χ g h = if N ≤ chiVal χ g + chiVal χ h then 1 else 0 := by
  have h1 := chiVal_lt χ g
  have h2 := chiVal_lt χ h
  have hN : 0 < N := Nat.pos_of_neZero N
  unfold chiCarry
  split_ifs with hle
  · apply Nat.div_eq_of_lt_le <;> omega
  · exact Nat.div_eq_of_lt (by omega)

end Chi
end ResFC
end LocalLevel
end ExtCitation
end P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
