public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uCore_le_and_isElemAbelian (hchar : IsCharTwoType G) {M T : Subgroup G}
    (hM : IsTwoLocal M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    uCore M T ≤ pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ∧ IsElemAbelian 2 (uCore M T) := by
  have hX := omegaOneCenterIn_le_inf_centralizer T
  have hXe : IsElemAbelian 2 (CFSG.RankThree.PartOne.omegaOneCenterIn T) :=
    ⟨⟨⟨fun a b => Subtype.ext ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp
      b.2).2.1 a (hX a.2).1)⟩⟩,
      fun x hx => (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hx).2.2⟩
  exact ⟨iSup_conj_le_pCoreOf_inf_centralizer hchar hM hT (fun _ h => (hX h).1)
    (fun _ h => (hX h).2), isElemAbelian_iSup_conj hchar hM hT (fun _ h => (hX h).1)
    (fun _ h => (hX h).2) hXe⟩

end CFSG.LocalAnalysis.RankThreeUC
end
