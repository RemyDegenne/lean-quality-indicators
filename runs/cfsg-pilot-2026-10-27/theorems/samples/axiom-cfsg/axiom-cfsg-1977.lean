public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit

theorem nonempty_quotCenter_equiv_swapDiag {X : Type} [Group X] {K : Subgroup X} {t : X}
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X))
    (hK : CFSG.IsQuasisimple ↥K) :
    Nonempty (↥K ⧸ center ↥K ≃*
      ↥(swapDiag K t hc).range ⧸ center ↥(swapDiag K t hc).range) := by
  have hker : (swapDiag K t hc).rangeRestrict.ker ≤ center ↥K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_swapDiag_le_center hc
  exact nonempty_quotCenter_equiv_of_central_ker hK (swapDiag K t hc).rangeRestrict
    (swapDiag K t hc).rangeRestrict_surjective hker

end CFSG.OddStandard.HigherRank.F3
end
