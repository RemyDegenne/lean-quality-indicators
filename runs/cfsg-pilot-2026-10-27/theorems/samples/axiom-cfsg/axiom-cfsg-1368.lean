public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem le_of_perfect_subgroup_of_three_le_pRank (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : KIDExcluded k) (h75 : Step75 k) (hS : StronglyEmbeddedSolvable)
    {H X : Subgroup G} (hH : H ≠ ⊤) (hXHM : X ≤ H ⊓ k.M)
    (hXperf : ⁅X, X⁆ = X) (hXrank : 3 ≤ CFSG.Open.pRank k.p X) : H ≤ k.M := by
  by_contra hHM
  have hmono : CFSG.Open.pRank k.p X ≤ CFSG.Open.pRank k.p (H ⊓ k.M) :=
    CFSG.SectionRank.pRank_mono k.prime.one_lt hXHM
  have hHcfg : Config k H := ⟨hH, hHM, by omega⟩
  have hbound := k.pRank_le_two_of_perfect_in_config h5 hno h75 hS hHcfg hXHM hXperf
  omega

end Sec7Core4
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
end
