public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open scoped commutatorElement

namespace Item1119StepsProof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sec11K_ne_bot (h : Sec11Data G A c L a R Y d x s r g) : sec11K L a ≠ ⊥ := by
  obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  exact fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)

end Data
end Item1119StepsProof
end CFSG.RankThree.PartTwo.Sec11
end
