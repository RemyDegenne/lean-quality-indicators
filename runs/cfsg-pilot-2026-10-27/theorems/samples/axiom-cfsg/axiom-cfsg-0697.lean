public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Fan86.Univ

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] {M T L : Subgroup G}

theorem MS93ConclASW.of_case10 (h : MS93Case10 M L) : MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

end CFSG.Quasithin.SzMSW
end
