public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

section Core

variable {G : Type} [Group G] [Finite G]

theorem conj_injective_of_center_eq_bot {X : Type*} [Group X]
    (h : Subgroup.center X = ⊥) : Function.Injective (MulAut.conj : X →* MulAut X) :=
  (MonoidHom.ker_eq_bot_iff _).mp ((ker_conj_eq_center X).trans h)

end Core
end CFSG.RankThree.PartTwo.Sec8.Hering418
end
