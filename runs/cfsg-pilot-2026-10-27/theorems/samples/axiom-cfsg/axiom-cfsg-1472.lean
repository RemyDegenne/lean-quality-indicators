public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_25_H2_hall_of
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h17_20 : R17_20At D V₀ V) (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hSg : UC6S846.SigmaStd D) (h880 : F08.R880 D)
    (hJ2aut : K_J2_aut_five_rank) :
    Gap17_25_H2_hall D V₀ V L c.hyp125.isElemAbelian := by
  intro _hV0 _hP hJ2 hsig
  exact exists_H2_of_J2 c h17_20 h17_22 h17_23 hSg h880 hJ2aut hJ2 hsig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
end
