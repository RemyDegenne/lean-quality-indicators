public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n

open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)

include H

section Root

theorem tim78_4_13 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) :
    (∀ g : G, conjSubgroup g B ≤ M → conjSubgroup g B ≤ P) ∧
      (∀ b ∈ B, ∀ g : G, g * b * g⁻¹ ∈ M → g * b * g⁻¹ ∈ P) :=
  H.tim78_4_13_of_4_12 hCen hU hRT h48 (H.tim78_4_12 hCen hU hRT h48)

end Root
end Hyp4
end CFSG.RankThree.GF2n.Tim78
end
