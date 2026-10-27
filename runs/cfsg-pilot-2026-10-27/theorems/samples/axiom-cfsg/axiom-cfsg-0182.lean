public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open CFSG.RankThree.PartTwo.Sec4.Ronan148V

open CFSG.SignalizerFunctorTheorem (IsSectionOf)

variable {S S' G G' A B : Type*} [Group S] [Group S'] [Group G] [Group G'] [Group A] [Group B]

theorem isSec_trans (h : IsSec S G') (h' : IsSec G' G) : IsSec S G :=
  IsSectionOf.trans (X := S) (Y := G') (Z := G) h h'

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
end
