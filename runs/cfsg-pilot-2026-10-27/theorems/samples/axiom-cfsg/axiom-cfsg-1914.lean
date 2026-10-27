public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.Open Subgroup

open CFSG.Blueprint (LieModel)

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)

open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder)

theorem kstar_false_of_sp44
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J X : Type} [Group J] [Finite J] [Group X] (hq : CFSG.Open.IsQuasisimple J)
    (hodd : Odd (Nat.card ↥(Subgroup.center J))) (hZ : Nontrivial ↥(Subgroup.center J))
    (e : J ⧸ Subgroup.center J ≃* X) (h : IsSp4 X 2) : False := by
  exact w183K3Shape3_false_of_models hGA hq hodd hZ e
    (w183K3Shape3_models_of_blueprint h (by decide)) (by decide)

end W183K3
end CFSG.LocalAnalysis.WeakClosure81
end
