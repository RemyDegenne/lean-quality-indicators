public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.ABGLocalTools (IsSylowOf)

open scoped commutatorElement

section Main

namespace Item1116Proof

variable {G : Type} [Group G] [Finite G]

theorem c_not_mem_thetaQuotCentralizer (h118 : Item118) {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) : c ∉ Sec4.thetaQuotCentralizer Y := by
  intro hc
  obtain ⟨-, -, hCA⟩ := h118 G A c L a R Y h.toSec11Std d g h.inf_eq h.closure_eq h.g_mem.2
    h.g_not_mem h.conj_mem
  have h1 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer h.mem_A hc
  rw [hCA] at h1
  exact (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).1 h1

end Item1116Proof
end Main
end CFSG.RankThree.PartTwo.Sec11
end
