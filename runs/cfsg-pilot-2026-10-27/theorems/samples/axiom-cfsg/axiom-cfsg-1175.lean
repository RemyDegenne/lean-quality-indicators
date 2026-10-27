public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff7_aux_quots (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    ∀ k : Fin 6, ∃ _ : ((ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)).Normal,
      IsElementaryAbelian 2 (↥(ffSeries φ t i k.succ) ⧸
        (ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)) := by
  intro k
  fin_cases k
  · exact sixFF_ff7_aux_q0 hS
  · exact sixFF_ff7_aux_q1 hH
  · exact sixFF_ff7_aux_q2 hH
  · exact sixFF_ff7_aux_q3 hS hH
  · exact sixFF_ff7_aux_q4 hH
  · exact sixFF_ff7_aux_q5 hH

end Steps
end SingleCommParts
end CFSG.LocalAnalysis.SymplecticFourStandard
end
