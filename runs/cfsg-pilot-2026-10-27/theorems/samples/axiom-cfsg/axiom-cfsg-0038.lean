public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

open Aux

theorem blockU_le_Dc (h : NatBlock L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : blockU L ≤ Dc L T := fun v hv =>
  ⟨NatBlock.blockU_le_sylow hLM hMN hT hv,
    Subgroup.mem_centralizer_iff.2 fun w hw => h.blockU_comm w hw v hv⟩

end CFSG.CGT.PushingUpLit.T2KSW
end
