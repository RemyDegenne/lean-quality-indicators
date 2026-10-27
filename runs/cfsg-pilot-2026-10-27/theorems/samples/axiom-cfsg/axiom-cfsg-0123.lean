public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBWeylRowResRest_small_false_nbr
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hnb : GGNbr p B x D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => GGTBWeylRowResRest p lab ∧ GGTBResSmallLabel p lab)
      p Bs K) : False :=
  not_largeEvenMarking_resSmall (X := ↥K) hcfg.1.2.2.2.2.2.1.1 hcfg.1.2.2.2.2.2.1.2.1
    (ggInnerDiagOnLabel_nbr_pRank_ge_three hcfg hnb hK)

end CFSG.StandardType
end
