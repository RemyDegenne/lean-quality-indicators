public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

section MinCexConj

variable {Ω : Set (Subgroup G)} {p f : ℕ} [Fact p.Prime] [Finite G]

set_option linter.unusedSectionVars false in
theorem EStand.conj {K R W : Subgroup G} {S : Sylow 2 G} (h : EStand p f Ω K S R W) (g : G) :
    EStand p f Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W) where
  odd := h.odd
  five := h.five
  hyp := h.hyp
  below := h.below
  mem := h.hyp.conjInvariant g K h.mem
  aEmpty := aEmpty_conj h.hyp.conjInvariant h.aEmpty g
  twin := E187C.twin_conj h.hyp.conjInvariant h.twin g
  hR := E187C.hR_conj h.hyp.conjInvariant h.hR g
  hW := E187C.hW_conj h.hyp.conjInvariant h.hW g

end MinCexConj
end CFSG.ClassicalInvolution.Asc77
end
