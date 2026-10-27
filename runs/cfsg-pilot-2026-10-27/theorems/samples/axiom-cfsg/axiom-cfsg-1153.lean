public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

variable {G : Type} [Group G] [Finite G]

namespace Equivariance

theorem statedClassicalModel_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : StatedLieTag} {n q f : ℕ} (h : StatedClassicalModel A t n q f) :
    StatedClassicalModel B t n q f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

end Equivariance
end CFSG.RankThree.PartOne
end
