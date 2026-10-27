public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22pwu_swap {D : Data G} {L K K' : Subgroup G} (hL : L ∈ calL D.T D.M) (hKL : K ≤ L)
    (g : ↥D.T) (hg : uc22p20bCj (g : G) K = K') (x : Bar2 L) :
    x ∈ uc22pwuImg L K ↔ uc22pwIndHom L D.T hL.1 g x ∈ uc22pwuImg L K' := by
  rw [← hg]
  exact uc22pwu_mem_img_iff hKL (hL.1 g.2) x

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
