public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem bBar_conjClosure_le_two {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : S17.Ctx17_6 D V₀ V L r q) (h77 : Inputs1719.W4Lem7_7)
    (h106 : Inputs1719.W4Lem10_6Q)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥) (hq : 3 < q) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 2 := by
  refine bBar_conjClosure_le_of_candidate_bound hC h77 hL1 fun g n hn => ?_
  exact (aCandidate_barSub_conj_bounds hC h106 hL1 hn.some).2 hq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
