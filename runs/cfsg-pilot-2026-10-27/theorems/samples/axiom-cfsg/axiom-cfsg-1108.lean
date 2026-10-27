public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial

open CFSG.RankThree.PartOne.Torsion37

variable {G : Type} [Group G]

namespace LayerCore

variable {p : ℕ} {A L K : Subgroup G} {b : G}

theorem K_le_centralizer (hd : LayerCore p A L b K) : K ≤ Subgroup.centralizer ({b} : Set G) :=
  hd.K_le_inf.trans inf_le_right

end LayerCore
end CFSG.RankThree.PartOne
end
